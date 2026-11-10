module

public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent.ColimitRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Colimits and maps of finite presentation: descent of linear maps and isomorphisms

Let `R = colim_i R_i` be a directed colimit of `A`-algebras. A linear map out of a
finitely presented module after base change to `R` descends to some `R_i`, and a map from a
finite to a finitely presented module that becomes an isomorphism after base change to `R`
is an isomorphism after base change to some `R_i`. The last section restates the four
descent statements for a filtered colimit of rings, presented as a cocone over a diagram
`F : J ⥤ CommRingCat` whose underlying cocone of types is colimiting.

## Main results

* `statement_three`: if `N` is finitely presented, any `R`-map `v : N ⊗_A R → M ⊗_A R`
  descends to an `R_i`-map for some `i`.
* `statement_four`: if `M` is finite, `N` finitely presented, and `u : M → N` becomes an
  isomorphism after base change to `R`, it is an isomorphism after base change to some
  `R_i`.
* `exists_baseChange_eq_of_isColimit`, `exists_surjective_baseChange_of_isColimit`,
  `exists_linearMap_of_isColimit`, `exists_bijective_baseChange_of_isColimit`: the four
  statements for a filtered colimit of rings.
-/

@[expose] public section

universe u v

@[expose] public section


open scoped TensorProduct

namespace Stacks.FinitePresentation.ColimitDescent

/-- `transMod` composes along `i ≤ j ≤ k`. -/
private theorem transMod_transMod {A : Type*} [CommRing A] {ι : Type*} [Preorder ι]
    {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j) (htrans : TransitionSystem φ) {P : Type*}
    [AddCommGroup P] [Module A P] {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (w : (R i) ⊗[A] P) :
    transMod φ P hjk (transMod φ P hij w) = transMod φ P (le_trans hij hjk) w := by
  induction w using TensorProduct.inductionOn with
  | tmul r m => simp only [transMod_tmul, htrans.trans hij hjk r]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `canonMod` is unchanged by composing with a transition map. -/
private theorem canonMod_transMod {A : Type*} [CommRing A] {ι : Type*} [Preorder ι]
    {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)] {S : Type*} [CommRing S]
    [Algebra A S] (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j) (ψ : ∀ i, R i →ₐ[A] S)
    (hcocone : IsCoconeAlg φ ψ) {P : Type*} [AddCommGroup P] [Module A P] {i j : ι} (hij : i ≤ j)
    (w : (R i) ⊗[A] P) :
    canonMod ψ P j (transMod φ P hij w) = canonMod ψ P i w := by
  induction w using TensorProduct.inductionOn with
  | tmul r m => simp only [transMod_tmul, canonMod_tmul, hcocone hij r]
  | add x y hx hy => simp only [map_add, hx, hy]

section Statements

variable {A : Type*} [CommRing A]
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable {S : Type*} [CommRing S] [Algebra A S]
variable (φ : ∀ ⦃i j : ι⦄, i ≤ j → R i →ₐ[A] R j)
variable (ψ : ∀ i, R i →ₐ[A] S)

/-- Two `A`-linear maps from a finite module into `R i ⊗ Q` that agree after `canonMod` agree
after some transition map, and after every later one. -/
private theorem exists_transMod_eq_of_canonMod_eq (htrans : TransitionSystem φ)
    {P Q : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [AddCommGroup Q]
    [Module A Q] (hcolim : IsModuleColimit φ ψ Q) (i : ι) (f g : P →ₗ[A] (R i) ⊗[A] Q)
    (h : ∀ p, canonMod ψ Q i (f p) = canonMod ψ Q i (g p)) :
    ∃ (j₀ : ι) (h₀ : i ≤ j₀), ∀ (j : ι) (hj : j₀ ≤ j) (p : P),
      transMod φ Q (h₀.trans hj) (f p) = transMod φ Q (h₀.trans hj) (g p) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := P)
  have hmono : ∀ ⦃j k : ι⦄, j ≤ k → ∀ p,
      (∃ hij : i ≤ j, transMod φ Q hij (f p) = transMod φ Q hij (g p)) →
        ∃ hik : i ≤ k, transMod φ Q hik (f p) = transMod φ Q hik (g p) :=
    fun j k hjk p ⟨hij, hz⟩ => ⟨hij.trans hjk, by
      rw [← transMod_transMod φ htrans hij hjk, ← transMod_transMod φ htrans hij hjk, hz]⟩
  classical
  obtain ⟨j₀, hj₀⟩ := exists_forall_one_tmul_eq _ hmono s fun p _ =>
    hcolim.exists_eq_of_canonMod_eq i _ _ (h p)
  obtain ⟨k, hik, hj₀k⟩ := directed_of (· ≤ ·) i j₀
  refine ⟨k, hik, fun j hj p => ?_⟩
  refine LinearMap.congr_fun (LinearMap.ext_on (f := transMod φ Q (hik.trans hj) ∘ₗ f)
    (g := transMod φ Q (hik.trans hj) ∘ₗ g) hs fun p hp => ?_) p
  exact (hmono (hj₀k.trans hj) p (hj₀ p hp)).choose_spec

/-- A tensor `r ⊗ p` is `r` times `1 ⊗ p`. -/
private theorem tmul_eq_smul_one_tmul {B P : Type*} [CommRing B] [Algebra A B] [AddCommGroup P]
    [Module A P] (r : B) (p : P) : r ⊗ₜ[A] p = r • ((1 : B) ⊗ₜ[A] p) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- `B`-linear maps out of `B ⊗[A] P` are determined by their values on `1 ⊗ p`. -/
private theorem linearMap_ext_one_tmul {B P Q : Type*} [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] [Module B Q] [IsScalarTower A B Q]
    (f g : B ⊗[A] P →ₗ[B] Q)
    (h : ∀ p, f ((1 : B) ⊗ₜ[A] p) = g ((1 : B) ⊗ₜ[A] p)) : f = g :=
  TensorProduct.AlgebraTensorModule.ext fun r p => by
    rw [tmul_eq_smul_one_tmul, map_smul, map_smul, h]

/-- **Statement (3).** If `N` is a finitely presented `A`-module and
`v : N ⊗_A R → M ⊗_A R` is an `R`-module map, then there is some `i` and an
`R_i`-module map `v_i : N ⊗_A R_i → M ⊗_A R_i` whose base change along
`ψ i : R_i → S` (i.e. composition with the canonical identification maps)
recovers `v`.  Concretely, `v` composed with the canonical map for `N` equals
the canonical map for `M` composed with `v_i`. -/
@[stacks 05LI "(3)"]
theorem statement_three
    (htrans : TransitionSystem φ) (hcocone : IsCoconeAlg φ ψ)
    (hcolimM : IsModuleColimit φ ψ M)
    (hN : Module.FinitePresentation A N)
    (v : S ⊗[A] N →ₗ[S] S ⊗[A] M) :
    ∃ (i : ι) (vi : (R i) ⊗[A] N →ₗ[R i] (R i) ⊗[A] M),
      (v.restrictScalars A) ∘ₗ (canonMod ψ N i)
        = (canonMod ψ M i) ∘ₗ (vi.restrictScalars A) := by
  classical
  -- general helper_05li lemmas
  have canonMod_smulM : ∀ (i : ι) (r : R i)
      (y : (R i) ⊗[A] M), canonMod ψ M i (r • y) = (ψ i r) • canonMod ψ M i y := by
    intro i r y
    induction y using TensorProduct.inductionOn with
    | tmul a m =>
        rw [TensorProduct.smul_tmul']
        simp only [canonMod, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
          AlgHom.toLinearMap_apply]
        rw [TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  -- presentation of N
  obtain ⟨n, sgen, hspan⟩ := Module.Finite.exists_fin (R := A) (M := N)
  set e : (Fin n →₀ A) →ₗ[A] N := Finsupp.linearCombination A sgen with he_def
  have he : Function.Surjective e := by
    rw [← LinearMap.range_eq_top]
    rw [he_def, Finsupp.range_linearCombination]
    exact hspan
  have hKfg : (LinearMap.ker e).FG := Module.FinitePresentation.fg_ker e he
  obtain ⟨relset, hrel⟩ := hKfg
  -- e of single
  have he_single : ∀ k : Fin n, e (Finsupp.single k 1) = sgen k := by
    intro k
    rw [he_def, Finsupp.linearCombination_single, one_smul]
  -- STEP A: common index i₀ and lifts w_k
  set Q : ι → N → Prop := fun i x => ∃ w : (R i) ⊗[A] M, canonMod ψ M i w = v ((1:S) ⊗ₜ[A] x)
    with hQ
  have hmono : ∀ ⦃i j : ι⦄, i ≤ j → ∀ x, Q i x → Q j x := by
    intro i j hij x hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨transMod φ M hij w, ?_⟩
    rw [canonMod_transMod φ ψ hcocone hij w, hw]
  -- join over generators using exists_forall_one_tmul_eq style induction (inline)
  have hjoin : ∃ j, ∀ x ∈ (Finset.image sgen Finset.univ), Q j x := by
    refine exists_forall_one_tmul_eq Q hmono (Finset.image sgen Finset.univ) ?_
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨i, y, hy⟩ := hcolimM.jointly_surjective (v ((1:S) ⊗ₜ[A] sgen k))
    exact ⟨i, y, hy⟩
  obtain ⟨i₀, hi₀⟩ := hjoin
  have hwk : ∀ k : Fin n, Q i₀ (sgen k) := by
    intro k
    apply hi₀
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨k, rfl⟩
  set w : Fin n → (R i₀) ⊗[A] M := fun k => Classical.choose (hwk k) with hw_def
  have hwspec : ∀ k, canonMod ψ M i₀ (w k) = v ((1:S) ⊗ₜ[A] sgen k) := by
    intro k
    exact Classical.choose_spec (hwk k)
  -- c : F → R i₀ ⊗ M
  set c : (Fin n →₀ A) →ₗ[A] (R i₀) ⊗[A] M := Finsupp.linearCombination A w with hc_def
  have hc_single : ∀ k, c (Finsupp.single k 1) = w k := by
    intro k
    rw [hc_def, Finsupp.linearCombination_single, one_smul]
  -- d-identity at i₀: canonMod ψ M i₀ (c x) = v (1 ⊗ e x)
  have hd : ∀ x : (Fin n →₀ A), canonMod ψ M i₀ (c x) = v ((1:S) ⊗ₜ[A] e x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [map_add, hp, hq, TensorProduct.tmul_add]
    | single k a =>
        have hLHS : c (Finsupp.single k a) = a • w k := by
          rw [hc_def, Finsupp.linearCombination_single]
        have hRHS : e (Finsupp.single k a) = a • sgen k := by
          rw [he_def, Finsupp.linearCombination_single]
        rw [hLHS, hRHS, map_smul, hwspec k, TensorProduct.tmul_smul,
          LinearMap.map_smul_of_tower]
  -- relset ⊆ ker e
  have hrel_sub : ∀ ρ ∈ relset, e ρ = 0 := by
    intro ρ hρ
    have : ρ ∈ LinearMap.ker e := by
      rw [← hrel]; exact Submodule.subset_span hρ
    rwa [LinearMap.mem_ker] at this
  -- STEP C: each relation's image vanishes after enlarging the index
  set Q' : ι → (Fin n →₀ A) → Prop :=
    fun j' ρ => ∃ (h : i₀ ≤ j'), transMod φ M h (c ρ) = 0 with hQ'
  have hmono' : ∀ ⦃i j : ι⦄, i ≤ j → ∀ ρ, Q' i ρ → Q' j ρ := by
    intro i j hij ρ hρ
    obtain ⟨h, hz⟩ := hρ
    refine ⟨le_trans h hij, ?_⟩
    rw [← transMod_transMod φ htrans h hij, hz, map_zero]
  have hs' : ∀ ρ ∈ relset, ∃ j', Q' j' ρ := by
    intro ρ hρ
    have hcm : canonMod ψ M i₀ (c ρ) = canonMod ψ M i₀ (0 : (R i₀) ⊗[A] M) := by
      rw [hd ρ, hrel_sub ρ hρ, TensorProduct.tmul_zero, map_zero, map_zero]
    obtain ⟨jρ, hjρ, hz⟩ := hcolimM.exists_eq_of_canonMod_eq i₀ (c ρ) 0 hcm
    refine ⟨jρ, hjρ, ?_⟩
    rwa [map_zero] at hz
  obtain ⟨j₀, hj₀⟩ := exists_forall_one_tmul_eq Q' hmono' relset hs'
  obtain ⟨j, hi₀j, hj₀j⟩ := directed_of (· ≤ ·) i₀ j₀
  -- cj : F → R j ⊗ M
  set cj : (Fin n →₀ A) →ₗ[A] (R j) ⊗[A] M := (transMod φ M hi₀j) ∘ₗ c with hcj_def
  have hcj_apply : ∀ x, cj x = transMod φ M hi₀j (c x) := fun x => rfl
  have hcj_rel : ∀ ρ ∈ relset, cj ρ = 0 := by
    intro ρ hρ
    obtain ⟨h₀, hz₀⟩ := hj₀ ρ hρ
    rw [hcj_apply, ← transMod_transMod φ htrans h₀ hj₀j, hz₀, map_zero]
  -- cj vanishes on all of ker e
  have hcj_span : ∀ κ ∈ Submodule.span A (relset : Set (Fin n →₀ A)), cj κ = 0 := by
    intro κ hmem
    induction hmem using Submodule.span_induction with
    | mem x hx => exact hcj_rel x hx
    | zero => rw [map_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have hcj_vanish : ∀ κ : (Fin n →₀ A), e κ = 0 → cj κ = 0 := fun κ hκ =>
    hcj_span κ (by rw [hrel]; exact LinearMap.mem_ker.mpr hκ)
  -- surjective ej
  have hej : Function.Surjective (LinearMap.baseChange (R j) e) :=
    LinearMap.baseChange_surjective (R j) he
  -- kernel containment
  have hker_le : LinearMap.ker (LinearMap.baseChange (R j) e) ≤
      LinearMap.ker (LinearMap.liftBaseChange (R j) cj) := by
    have hex : Function.Exact ⇑(LinearMap.ker e).subtype ⇑e := LinearMap.exact_subtype_ker_map e
    have htens := lTensor_exact (R := A) (R j) hex he
    have hkereq := htens.linearMap_ker_eq
    have hcomp : ∀ y : (R j) ⊗[A] (LinearMap.ker e),
        (LinearMap.liftBaseChange (R j) cj) ((LinearMap.lTensor (R j) (LinearMap.ker e).subtype)
            y) = 0 := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul r κ =>
          rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul]
          have hκ : cj (κ : (Fin n →₀ A)) = 0 :=
            hcj_vanish κ.val (by have := κ.property; rwa [LinearMap.mem_ker] at this)
          simp only [Submodule.subtype_apply]
          rw [hκ, smul_zero]
      | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hbc : (LinearMap.baseChange (R j) e) z = (LinearMap.lTensor (R j) e) z := by
      rw [LinearMap.baseChange_eq_lTensor]
    rw [hbc] at hz
    have hzmem : z ∈ LinearMap.ker (LinearMap.lTensor (R j) e) := LinearMap.mem_ker.mpr hz
    rw [hkereq] at hzmem
    obtain ⟨y, hy⟩ := hzmem
    rw [← hy]
    exact hcomp y
  -- factor gj through ej to get vi
  set gj : (R j) ⊗[A] (Fin n →₀ A) →ₗ[R j] (R j) ⊗[A] M := LinearMap.liftBaseChange (R j) cj
    with hgj_def
  set ej : (R j) ⊗[A] (Fin n →₀ A) →ₗ[R j] (R j) ⊗[A] N := LinearMap.baseChange (R j) e
    with hej_def
  set vi : (R j) ⊗[A] N →ₗ[R j] (R j) ⊗[A] M :=
    (ej.ker.liftQ gj hker_le) ∘ₗ (ej.quotKerEquivOfSurjective hej).symm.toLinearMap with hvi_def
  have hfact : vi ∘ₗ ej = gj := by
    apply LinearMap.ext
    intro x
    simp only [hvi_def, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (ej.quotKerEquivOfSurjective hej).symm (ej x) = Submodule.Quotient.mk x from ?_]
    · rw [Submodule.liftQ_apply]
    · rw [LinearEquiv.symm_apply_eq]; rfl
  -- master identity: canonMod M j (gj z) = v (canonMod N j (ej z))
  have master : ∀ z : (R j) ⊗[A] (Fin n →₀ A),
      canonMod ψ M j (gj z) = v (canonMod ψ N j (ej z)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
        rw [hgj_def, LinearMap.liftBaseChange_tmul, canonMod_smulM,
          hcj_apply, canonMod_transMod φ ψ hcocone hi₀j (c x), hd x,
          hej_def, LinearMap.baseChange_tmul, canonMod_tmul]
        rw [tmul_eq_smul_one_tmul (ψ j r), map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- conclude
  refine ⟨j, vi, ?_⟩
  apply LinearMap.ext
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
  obtain ⟨z, rfl⟩ := hej y
  have hgz : vi (ej z) = gj z := by rw [← LinearMap.comp_apply, hfact]
  rw [hgz]
  exact (master z).symm

/-- **Statement (4).** If `M` is finite, `N` is finitely presented, and
`u : M → N` has base change to `R` an isomorphism, then its base change to some
`R_i` is an isomorphism. -/
@[stacks 05LI "(4)"]
theorem statement_four
    (htrans : TransitionSystem φ) (hcocone : IsCoconeAlg φ ψ)
    (hcolimM : IsModuleColimit φ ψ M) (hcolimN : IsModuleColimit φ ψ N)
    (hM : Module.Finite A M) (hN : Module.FinitePresentation A N)
    (u : M →ₗ[A] N)
    (h : Function.Bijective (LinearMap.baseChange S u)) :
    ∃ i : ι, Function.Bijective (LinearMap.baseChange (R i) u) := by
  -- Proof sketch (Stacks 05LI(4)).  `baseChange S u` is bijective; let
  -- `e := LinearEquiv.ofBijective (baseChange S u) h`, an `S`-linear iso
  -- `S ⊗ M ≃ S ⊗ N` (it is `S`-linear: `baseChange S u = (baseChange S u).restrictScalars A`
  -- of the genuinely `S`-linear `TensorProduct.map`/`AlgebraTensorModule` base
  -- change; use that `S`-linear structure).  Set `v := e.symm`, an `S`-linear
  -- map `S ⊗ N → S ⊗ M`.
  --
  -- STEP A (descend `v` by statement_three).  `N` is finitely presented and we
  -- have `hcolimM, hcolimN`, so `statement_three φ ψ htrans hcocone hcolimM
  -- hcolimN hN v` yields `i₂` and `vi : R i₂ ⊗ N →ₗ[R i₂] R i₂ ⊗ M` with
  --   `v.restrictScalars A ∘ₗ canonMod ψ N i₂ = canonMod ψ M i₂ ∘ₗ vi.restrictScalars A`.   (★)
  --
  -- STEP B (the two composites are the identity over `S`).  Over `S`,
  -- `baseChange S u` and `v` are mutually inverse, so:
  --   * `baseChange S u ∘ canonMod ψ M i₂ ∘ vi = canonMod ψ M i₂`  (apply `baseChange S u`
  --     to (★) and use `v` = inverse, plus `canonMod_baseChange`), and
  --   * `(canonMod ψ N i₂) ∘ (baseChange (R i₂) u) ... ` similarly.
  -- Concretely both `vi ∘ baseChange (R i₂) u` and `baseChange (R i₂) u ∘ vi`
  -- become the respective identities after applying `canonMod` (i.e. after
  -- base change to `S`), using `canonMod_baseChange` to move `baseChange` past
  -- `canonMod` and (★) to substitute `v`.
  --
  -- STEP C (descend the two identities by statement_one).  `M` is finite and
  -- `N` is finite (finitely presented ⟹ finite), so applying `statement_one`
  -- twice — once to the pair `(vi ∘ baseChange (R i₂) u, id)` as maps
  -- `M → M`-base-changed [needs both to be base changes of `A`-maps; obtain via
  -- naturality], once to `(baseChange (R i₂) u ∘ vi, id)` as maps `N → N` —
  -- gives `j ≥ i₂` where both composites equal the identity at `R j`.  (The
  -- precise statement_one application is to the `A`-linear maps underlying the
  -- composites; `statement_one` descends an equality of base-changed maps, which
  -- is what STEP B provides over `S`.)
  --
  -- STEP D (conclude bijectivity).  At that `j`, `baseChange (R j) u` has a
  -- two-sided inverse `transMod-transported vi`, hence is bijective:
  -- `Function.bijective_iff_has_inverse`.  Provide `j`.
  classical
  have hNfin : Module.Finite A N := inferInstance
  -- The `S`-linear isomorphism `e := baseChange S u` and its inverse `v`.
  set e : S ⊗[A] M ≃ₗ[S] S ⊗[A] N := LinearEquiv.ofBijective (LinearMap.baseChange S u) h
    with he_def
  set v : S ⊗[A] N →ₗ[S] S ⊗[A] M := e.symm.toLinearMap with hv_def
  -- STEP A: descend `v` by statement_three.
  obtain ⟨i₂, vi, hvi⟩ := statement_three φ ψ htrans hcocone hcolimM hN v
  have hvi' : ∀ z : (R i₂) ⊗[A] N, v (canonMod ψ N i₂ z) = canonMod ψ M i₂ (vi z) := by
    intro z
    have := congrArg (fun f => f z) hvi
    simpa using this
  -- STEP B: the two composites become identities after `canonMod`, at generators.
  have hleft_canon : ∀ m : M,
      canonMod ψ M i₂ (vi (LinearMap.baseChange (R i₂) u ((1 : R i₂) ⊗ₜ[A] m)))
        = canonMod ψ M i₂ ((1 : R i₂) ⊗ₜ[A] m) := by
    intro m
    rw [← hvi' (LinearMap.baseChange (R i₂) u ((1 : R i₂) ⊗ₜ[A] m)), canonMod_baseChange, hv_def]
    exact e.symm_apply_apply (canonMod ψ M i₂ ((1 : R i₂) ⊗ₜ[A] m))
  have hright_canon : ∀ n : N,
      canonMod ψ N i₂ (LinearMap.baseChange (R i₂) u (vi ((1 : R i₂) ⊗ₜ[A] n)))
        = canonMod ψ N i₂ ((1 : R i₂) ⊗ₜ[A] n) := by
    intro n
    rw [canonMod_baseChange, ← hvi' ((1 : R i₂) ⊗ₜ[A] n), hv_def]
    exact e.apply_symm_apply (canonMod ψ N i₂ ((1 : R i₂) ⊗ₜ[A] n))
  -- STEP C: descend the two identities to a common index `j ≥ i₂`.
  obtain ⟨jL, hjL, hL⟩ := exists_transMod_eq_of_canonMod_eq φ ψ htrans hcolimM i₂
    ((vi.restrictScalars A) ∘ₗ ((LinearMap.baseChange (R i₂) u).restrictScalars A) ∘ₗ
      (TensorProduct.mk A (R i₂) M) 1) (TensorProduct.mk A (R i₂) M 1) hleft_canon
  obtain ⟨jR, hjR, hR⟩ := exists_transMod_eq_of_canonMod_eq φ ψ htrans hcolimN i₂
    (((LinearMap.baseChange (R i₂) u).restrictScalars A) ∘ₗ (vi.restrictScalars A) ∘ₗ
      (TensorProduct.mk A (R i₂) N) 1) (TensorProduct.mk A (R i₂) N 1) hright_canon
  obtain ⟨j, hjLj, hjRj⟩ := directed_of (· ≤ ·) jL jR
  have hi₂j : i₂ ≤ j := hjL.trans hjLj
  have hLE : ∀ m : M,
      transMod φ M hi₂j (vi (LinearMap.baseChange (R i₂) u ((1 : R i₂) ⊗ₜ[A] m)))
        = transMod φ M hi₂j ((1 : R i₂) ⊗ₜ[A] m) := hL j hjLj
  have hRE : ∀ n : N,
      transMod φ N hi₂j (LinearMap.baseChange (R i₂) u (vi ((1 : R i₂) ⊗ₜ[A] n)))
        = transMod φ N hi₂j ((1 : R i₂) ⊗ₜ[A] n) := hR j hjRj
  -- STEP D: build the inverse `vij` at level `j` and conclude bijectivity.
  set vi0 : N →ₗ[A] (R j) ⊗[A] M :=
    (transMod φ M hi₂j).comp ((vi.restrictScalars A).comp ((TensorProduct.mk A (R i₂) N) 1))
    with hvi0_def
  have hvi0_apply : ∀ n : N, vi0 n = transMod φ M hi₂j (vi ((1 : R i₂) ⊗ₜ[A] n)) := fun n => rfl
  set vij : (R j) ⊗[A] N →ₗ[R j] (R j) ⊗[A] M := LinearMap.liftBaseChange (R j) vi0
    with hvij_def
  have hvij_tmul : ∀ (r : R j) (n : N), vij (r ⊗ₜ[A] n) = r • vi0 n := by
    intro r n; rw [hvij_def, LinearMap.liftBaseChange_tmul]
  have hcomp_left : ∀ m : M,
      vij (LinearMap.baseChange (R j) u ((1 : R j) ⊗ₜ[A] m)) = (1 : R j) ⊗ₜ[A] m := by
    intro m
    rw [LinearMap.baseChange_tmul, hvij_tmul, one_smul, hvi0_apply]
    have h1 : (1 : R i₂) ⊗ₜ[A] u m = LinearMap.baseChange (R i₂) u ((1 : R i₂) ⊗ₜ[A] m) := by
      rw [LinearMap.baseChange_tmul]
    rw [h1, hLE m, transMod_one_tmul]
  have hcomp_right : ∀ n : N,
      LinearMap.baseChange (R j) u (vij ((1 : R j) ⊗ₜ[A] n)) = (1 : R j) ⊗ₜ[A] n := by
    intro n
    rw [hvij_tmul, one_smul, hvi0_apply, ← transMod_baseChange, hRE n, transMod_one_tmul]
  refine ⟨j, ?_⟩
  rw [Function.bijective_iff_has_inverse]
  refine ⟨vij, fun x => ?_, fun x => ?_⟩
  · exact LinearMap.congr_fun (linearMap_ext_one_tmul (vij ∘ₗ LinearMap.baseChange (R j) u)
      LinearMap.id hcomp_left) x
  · exact LinearMap.congr_fun (linearMap_ext_one_tmul (LinearMap.baseChange (R j) u ∘ₗ vij)
      LinearMap.id hcomp_right) x

end Statements

/-! ### Descent along a filtered colimit of rings

The four statements above are phrased for a family of `A`-algebras indexed by a directed
preorder.  A diagram `F : J ⥤ CommRingCat` over a filtered category, together with a cocone `c`
whose underlying cocone of types is colimiting, gives such a family: reindex `F` along a final
functor from a directed partial order, which exists by
`CategoryTheory.IsFiltered.exists_directed`.  The filtered-colimit description of elements and
of equalities then yields the colimit property for every `A`-module. -/

section RingCocone

open CategoryTheory CategoryTheory.Limits

universe w

/-- **A filtered category receives a final functor from a directed partial order.**  This is
`CategoryTheory.IsFiltered.exists_directed` for a filtered category which need not be small:
the index poset is produced for an equivalent small model. -/
@[sga "4 I 8.1.6" "more general", sga "4 I 8.1.7" "special case"]
private lemma exists_final_functor_partialOrder (J : Type v) [Category.{w} J] [IsFiltered J] :
    ∃ (α : Type (max v w)) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (D : α ⥤ J), D.Final := by
  obtain ⟨α, _, _, _, T, hT⟩ := IsFiltered.exists_directed (AsSmall.{max v w} J)
  have : T.Final := hT
  have : (AsSmall.down : AsSmall.{max v w} J ⥤ J).IsEquivalence :=
    (AsSmall.equiv (C := J)).isEquivalence_inverse
  exact ⟨α, inferInstance, inferInstance, inferInstance, T ⋙ AsSmall.down,
    Functor.final_comp_equivalence T AsSmall.down⟩

variable {A : Type*} [CommRing A] {J : Type v} [Category.{w} J]
  (F : J ⥤ CommRingCat.{u}) (c : Cocone F) [∀ i, Algebra A (F.obj i)] [Algebra A c.pt]
  (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j) (a : A),
    (F.map f).hom (algebraMap A (F.obj i) a) = algebraMap A (F.obj j) a)
  (hι : ∀ (i : J) (a : A),
    (c.ι.app i).hom (algebraMap A (F.obj i) a) = algebraMap A c.pt a)

/-- **Elements and equalities in a filtered colimit of rings are detected at a stage.**  If the
cocone of underlying types of a cocone over a filtered diagram of rings is colimiting, then
every element of the cocone point comes from a stage and two elements of a stage with the same
image are identified by a transition map. -/
lemma jointlySurjective_and_exists_map_eq_of_isColimit_forget {β : Type*} [Category β]
    [IsFiltered β] (G : β ⥤ CommRingCat.{u}) (d : Cocone G)
    (hunder : IsColimit ((forget CommRingCat).mapCocone d)) :
    (∀ x : d.pt, ∃ (i : β) (y : G.obj i), (d.ι.app i).hom y = x) ∧
      ∀ (i : β) (x y : G.obj i), (d.ι.app i).hom x = (d.ι.app i).hom y →
        ∃ (j : β) (f : i ⟶ j), (G.map f).hom x = (G.map f).hom y :=
  ⟨fun x => Types.jointly_surjective_of_isColimit hunder x,
    fun _ x y h => (Types.FilteredColimit.isColimit_eq_iff' hunder x y).mp h⟩

/-- **A transition map of the diagram, as a map of `A`-algebras.** -/
def transitionAlgHom {i j : J} (f : i ⟶ j) : F.obj i →ₐ[A] F.obj j where
  toRingHom := (F.map f).hom
  commutes' := hF f

/-- **A leg of the cocone, as a map of `A`-algebras.** -/
def legAlgHom (i : J) : F.obj i →ₐ[A] c.pt where
  toRingHom := (c.ι.app i).hom
  commutes' := hι i

/-- `transitionAlgHom F hF f` is `F.map f` on elements. -/
@[simp] lemma transitionAlgHom_apply {i j : J} (f : i ⟶ j) (x : F.obj i) :
    transitionAlgHom F hF f x = (F.map f).hom x := rfl

/-- `legAlgHom F c hι i` is the leg `c.ι.app i` on elements. -/
@[simp] lemma legAlgHom_apply (i : J) (x : F.obj i) :
    legAlgHom F c hι i x = (c.ι.app i).hom x := rfl

section Reindex

variable {α : Type*} [Preorder α] (D : α ⥤ J)

/-- **The transition maps of a reindexed diagram of algebras.**  Reindexing a diagram of rings
whose transition maps respect given `A`-algebra structures along a monotone functor from a
preorder gives a family of `A`-algebra maps indexed by the inequalities of that preorder. -/
def reindexedTransition : ∀ ⦃i j : α⦄, i ≤ j → F.obj (D.obj i) →ₐ[A] F.obj (D.obj j) :=
  fun _ _ hij => transitionAlgHom F hF (D.map (homOfLE hij))

/-- **The cocone maps of a reindexed diagram of algebras.**  The legs of a cocone over a diagram
of rings whose legs respect given `A`-algebra structures, read off at the stages picked out by a
functor from a preorder. -/
def reindexedLeg : ∀ i : α, F.obj (D.obj i) →ₐ[A] c.pt :=
  fun i => legAlgHom F c hι (D.obj i)

/-- `reindexedTransition F hF D hij` is `F.map (D.map (homOfLE hij))` on elements. -/
@[simp] lemma reindexedTransition_apply {i j : α} (hij : i ≤ j) (x : F.obj (D.obj i)) :
    reindexedTransition F hF D hij x = (F.map (D.map (homOfLE hij))).hom x := rfl

/-- `reindexedLeg F c hι D i` is the leg `c.ι.app (D.obj i)` on elements. -/
@[simp] lemma reindexedLeg_apply (i : α) (x : F.obj (D.obj i)) :
    reindexedLeg F c hι D i x = (c.ι.app (D.obj i)).hom x := rfl

/-- The reindexed transition maps satisfy the functoriality laws of a directed system. -/
lemma transitionSystem_reindexedTransition : TransitionSystem (reindexedTransition F hF D) where
  refl i x := by
    rw [reindexedTransition_apply,
      show homOfLE (le_refl i) = 𝟙 i from Subsingleton.elim _ _, D.map_id, F.map_id]
    rfl
  trans {i j k} hij hjk x := by
    have hmap : F.map (D.map (homOfLE hij)) ≫ F.map (D.map (homOfLE hjk)) =
        F.map (D.map (homOfLE (hij.trans hjk))) := by
      rw [← F.map_comp, ← D.map_comp,
        show (homOfLE hij ≫ homOfLE hjk : i ⟶ k) = homOfLE (hij.trans hjk) from
          Subsingleton.elim _ _]
    exact congrArg (fun q : F.obj (D.obj i) ⟶ F.obj (D.obj k) => q.hom x) hmap

/-- The reindexed cocone maps are compatible with the reindexed transition maps. -/
lemma isCoconeAlg_reindexedLeg :
    IsCoconeAlg (reindexedTransition F hF D) (reindexedLeg F c hι D) := by
  intro i j hij x
  exact congrArg (fun q : F.obj (D.obj i) ⟶ c.pt => q.hom x) (c.w (D.map (homOfLE hij)))

/-- A final reindexing of a diagram of rings keeps the underlying cocone of types colimiting. -/
noncomputable def isColimitForgetMapCoconeWhisker [D.Final]
    (hunder : IsColimit ((forget CommRingCat).mapCocone c)) :
    IsColimit ((forget CommRingCat).mapCocone (c.whisker D)) :=
  IsColimit.ofIsoColimit ((Functor.Final.isColimitWhiskerEquiv D _).symm hunder)
    (Functor.mapCoconeWhisker (forget CommRingCat)).symm

/-- **A module over a filtered colimit of rings is the colimit of its base changes.**  Let `F`
be a diagram of rings carrying compatible `A`-algebra structures, reindexed along a final
functor from a nonempty directed partial order, and let `c` be a cocone on it whose underlying
cocone of types is colimiting.  Then every `A`-module `P` satisfies the colimit property for
the reindexed family: the maps `F(D i) ⊗_A P → c.pt ⊗_A P` are jointly surjective and detect
equality up to a transition map. -/
@[ega "IV 11.2.6.1" "partial"]
theorem isModuleColimit_reindexed [IsDirected α (· ≤ ·)] [Nonempty α] [D.Final]
    (hunder : IsColimit ((forget CommRingCat).mapCocone c))
    (P : Type*) [AddCommGroup P] [Module A P] :
    IsModuleColimit (reindexedTransition F hF D) (reindexedLeg F c hι D) P := by
  obtain ⟨hrep, heq⟩ := jointlySurjective_and_exists_map_eq_of_isColimit_forget (D ⋙ F)
    (c.whisker D) (isColimitForgetMapCoconeWhisker F c D hunder)
  refine isModuleColimit_of_χ_bijective _ _ (transitionSystem_reindexedTransition F hF D)
    (isCoconeAlg_reindexedLeg F c hF hι D)
    (χ_bijective_of_colimit_data _ _ _ hrep fun i r t hrt => ?_) P
  obtain ⟨j, f, hf⟩ := heq i r t hrt
  exact ⟨j, leOfHom f, by
    rw [reindexedTransition_apply, reindexedTransition_apply,
      show homOfLE (leOfHom f) = f from Subsingleton.elim _ _]
    exact hf⟩

end Reindex

variable [IsFiltered J] (hunder : IsColimit ((forget CommRingCat).mapCocone c))

include hF hι hunder

/-- **Equality of base-changed maps out of a finite module over a filtered colimit of rings
already holds at a stage.**  This is `statement_one` for a diagram of rings with compatible
`A`-algebra structures whose cocone of underlying types is colimiting. -/
theorem exists_baseChange_eq_of_isColimit {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M] (f g : M →ₗ[A] N)
    (h : LinearMap.baseChange c.pt f = LinearMap.baseChange c.pt g) :
    ∃ i : J, LinearMap.baseChange (F.obj i) f = LinearMap.baseChange (F.obj i) g := by
  obtain ⟨α, _, _, _, D, hD⟩ := exists_final_functor_partialOrder J
  have : D.Final := hD
  obtain ⟨i, hi⟩ := statement_one (reindexedTransition F hF D) (reindexedLeg F c hι D)
    (isModuleColimit_reindexed F c hF hι D hunder N) inferInstance f g h
  exact ⟨D.obj i, hi⟩

/-- **Surjectivity of a base-changed map to a finite module over a filtered colimit of rings
already holds at a stage.**  This is `statement_two` for a diagram of rings with compatible
`A`-algebra structures whose cocone of underlying types is colimiting. -/
theorem exists_surjective_baseChange_of_isColimit {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (f : M →ₗ[A] N)
    (hf : Function.Surjective (LinearMap.baseChange c.pt f)) :
    ∃ i : J, Function.Surjective (LinearMap.baseChange (F.obj i) f) := by
  obtain ⟨α, _, _, _, D, hD⟩ := exists_final_functor_partialOrder J
  have : D.Final := hD
  obtain ⟨i, hi⟩ := statement_two (reindexedTransition F hF D) (reindexedLeg F c hι D)
    (transitionSystem_reindexedTransition F hF D) (isCoconeAlg_reindexedLeg F c hF hι D)
    (isModuleColimit_reindexed F c hF hι D hunder N) inferInstance f hf
  exact ⟨D.obj i, hi⟩

/-- **A linear map out of a finitely presented module after base change to a filtered colimit of
rings descends to a stage.**  This is `statement_three` for a diagram of rings with compatible
`A`-algebra structures whose cocone of underlying types is colimiting; the descended map is
compatible with the canonical maps of base changes. -/
theorem exists_linearMap_of_isColimit {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.FinitePresentation A N]
    (g : c.pt ⊗[A] N →ₗ[c.pt] c.pt ⊗[A] M) :
    ∃ (i : J) (gi : F.obj i ⊗[A] N →ₗ[F.obj i] F.obj i ⊗[A] M),
      g.restrictScalars A ∘ₗ
          TensorProduct.map (legAlgHom F c hι i).toLinearMap (LinearMap.id (R := A) (M := N)) =
        TensorProduct.map (legAlgHom F c hι i).toLinearMap (LinearMap.id (R := A) (M := M)) ∘ₗ
          gi.restrictScalars A := by
  obtain ⟨α, _, _, _, D, hD⟩ := exists_final_functor_partialOrder J
  have : D.Final := hD
  obtain ⟨i, gi, hgi⟩ := statement_three (reindexedTransition F hF D) (reindexedLeg F c hι D)
    (transitionSystem_reindexedTransition F hF D) (isCoconeAlg_reindexedLeg F c hF hι D)
    (isModuleColimit_reindexed F c hF hι D hunder M) inferInstance g
  exact ⟨D.obj i, gi, hgi⟩

/-- **Bijectivity of a base-changed map from a finite to a finitely presented module over a
filtered colimit of rings already holds at a stage.**  This is `statement_four` for a diagram of
rings with compatible `A`-algebra structures whose cocone of underlying types is colimiting. -/
theorem exists_bijective_baseChange_of_isColimit {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [Module.Finite A M] [Module.FinitePresentation A N]
    (f : M →ₗ[A] N) (hf : Function.Bijective (LinearMap.baseChange c.pt f)) :
    ∃ i : J, Function.Bijective (LinearMap.baseChange (F.obj i) f) := by
  obtain ⟨α, _, _, _, D, hD⟩ := exists_final_functor_partialOrder J
  have : D.Final := hD
  obtain ⟨i, hi⟩ := statement_four (reindexedTransition F hF D) (reindexedLeg F c hι D)
    (transitionSystem_reindexedTransition F hF D) (isCoconeAlg_reindexedLeg F c hF hι D)
    (isModuleColimit_reindexed F c hF hι D hunder M)
    (isModuleColimit_reindexed F c hF hι D hunder N) inferInstance inferInstance f hf
  exact ⟨D.obj i, hi⟩

end RingCocone

end Stacks.FinitePresentation.ColimitDescent
