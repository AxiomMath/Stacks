module

public import Mathlib.CategoryTheory.CofilteredSystem
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom.SystemLimits
import all StacksFrontier.RingTheory.Module.AdicSystem.Hom.SystemLimits

@[expose] public section

/-!
# Mittag-Leffler property of the `Hom` and `Isom` systems of adic reductions

The `Hom` and `Isom` systems of the adic reductions of finite modules over a Noetherian ring
are Mittag-Leffler and the comparison from the adic quotients of `Hom` has uniformly bounded
kernel and cokernel.  This gives Tag 09BB and its consequence Tag 09BC.
-/

/-! ## Tag 09BB -/

section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AdicSystem.HomComparison

universe u v w x

private lemma finite_free_hom_reduce_surjective
    {A : Type u} {G : Type x} {N : Type w} [CommRing A]
    [AddCommGroup N] [Module A N] (J : Ideal A)
    (g : (G →₀ A) →ₗ[A] (N ⧸ J • (⊤ : Submodule A N))) :
    ∃ f : (G →₀ A) →ₗ[A] N,
      (J • (⊤ : Submodule A N)).mkQ.comp f = g :=
  Module.projective_lifting_property
    (J • (⊤ : Submodule A N)).mkQ g (Submodule.mkQ_surjective _)

private lemma finite_presentation_finsupp
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (G R : Type u) (_ : Finite G) (_ : Finite R)
      (f : (G →₀ A) →ₗ[A] M)
      (g : (R →₀ A) →ₗ[A] (G →₀ A)),
      Function.Surjective f ∧ Function.Exact g f := by
  let : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have hpres : ∃ (pres : Module.Presentation.{u, u} A M),
      Finite pres.G ∧ Finite pres.R :=
    (Module.finitePresentation_iff_exists_presentation).mp inferInstance
  obtain ⟨pres, hG, hR⟩ := hpres
  refine ⟨pres.G, pres.R, hG, hR, pres.π, pres.toRelations.map,
    pres.surjective_π, ?_⟩
  rw [LinearMap.exact_iff, pres.toRelations.range_map, pres.ker_π]

private lemma quotient_isBaseChange
    {A : Type u} {N : Type v} [CommRing A]
    [AddCommGroup N] [Module A N] (J : Ideal A) :
    IsBaseChange (A ⧸ J)
      ((J • (⊤ : Submodule A N)).mkQ :
        N →ₗ[A] (N ⧸ J • (⊤ : Submodule A N))) := by
  let e : TensorProduct A (A ⧸ J) N ≃ₗ[A ⧸ J]
      (N ⧸ J • (⊤ : Submodule A N)) :=
    (TensorProduct.quotTensorEquivQuotSMul N J).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  exact IsBaseChange.of_equiv e fun x ↦ TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul J x

private noncomputable def finite_free_hom_quotient_equiv
    {A : Type u} {G : Type x} {N : Type w} [CommRing A]
    [Finite G] [AddCommGroup N] [Module A N] (J : Ideal A) :
    (((G →₀ A) →ₗ[A] N) ⧸
      J • (⊤ : Submodule A ((G →₀ A) →ₗ[A] N))) ≃ₗ[A]
      ((G →₀ A) →ₗ[A] (N ⧸ J • (⊤ : Submodule A N))) := by
  letI : Module.Finite A (G →₀ A) := inferInstance
  let e := IsBaseChange.linearMapRightBaseChangeEquiv (G →₀ A)
    (quotient_isBaseChange (N := N) J)
  exact (TensorProduct.quotTensorEquivQuotSMul
    ((G →₀ A) →ₗ[A] N) J).symm.trans (e.restrictScalars A)

private lemma finite_presentation_hom_kernel
    {A : Type u} {M : Type v} {N : Type w}
    [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    {G : Type u} {R : Type x}
    {f : (G →₀ A) →ₗ[A] M}
    {g : (R →₀ A) →ₗ[A] (G →₀ A)}
    (hf : Function.Surjective f) (hfg : Function.Exact g f) :
    Function.Exact (LinearMap.lcomp A N f)
      (LinearMap.lcomp A N g) ∧
      Function.Injective (LinearMap.lcomp A N f) :=
  ⟨LinearMap.exact_lcomp_of_exact_of_surjective N hfg hf,
    LinearMap.lcomp_injective_of_surjective f hf⟩

private lemma finite_free_hom_quotient_equiv_mk
    {A : Type u} {G : Type x} {N : Type w} [CommRing A]
    [Finite G] [AddCommGroup N] [Module A N] (J : Ideal A)
    (f : (G →₀ A) →ₗ[A] N) :
    finite_free_hom_quotient_equiv J (Submodule.Quotient.mk f) =
      (J • (⊤ : Submodule A N)).mkQ.comp f := by
  simp [finite_free_hom_quotient_equiv,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk,
    IsBaseChange.linearMapRightBaseChangeEquiv,
    IsBaseChange.linearMapRightBaseChangeHom]

private lemma finite_free_hom_mem_smul_iff
    {A : Type u} {G : Type x} {N : Type w} [CommRing A]
    [Finite G] [AddCommGroup N] [Module A N] (J : Ideal A)
    (f : (G →₀ A) →ₗ[A] N) :
    f ∈ J • (⊤ : Submodule A ((G →₀ A) →ₗ[A] N)) ↔
      (J • (⊤ : Submodule A N)).mkQ.comp f = 0 := by
  rw [← finite_free_hom_quotient_equiv_mk J f, (finite_free_hom_quotient_equiv J).map_eq_zero_iff]
  exact (Submodule.Quotient.mk_eq_zero _).symm

/-- Artin–Rees: an element of the image in `I ^ (n + c) • ⊤` has a preimage in `I ^ n • ⊤`. -/
private lemma exists_adic_smul_top_preimage
    {A L T : Type*} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup T] [Module A T] [Module.Finite A T]
    (I : Ideal A) (β : L →ₗ[A] T) :
    ∃ c : ℕ, ∀ n (x : L), β x ∈ I ^ (n + c) • (⊤ : Submodule A T) →
      ∃ z ∈ I ^ n • (⊤ : Submodule A L), β z = β x := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (I := I) (LinearMap.range β)
  refine ⟨c, fun n x hx => ?_⟩
  have hmem : β x ∈ (I ^ (n + c) • (⊤ : Submodule A T)) ⊓
      LinearMap.range β := ⟨hx, ⟨x, rfl⟩⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel] at hmem
  have h : β x ∈ I ^ n • LinearMap.range β :=
    (show I ^ n • ((I ^ c • (⊤ : Submodule A T)) ⊓ LinearMap.range β) ≤
      I ^ n • LinearMap.range β from smul_mono_right _ inf_le_right) hmem
  rwa [← Submodule.map_top β, ← Submodule.map_smul''] at h

private lemma exists_adic_preimage_bound
    {A L T : Type*} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup L] [Module A L]
    [AddCommGroup T] [Module A T] [Module.Finite A T]
    (I : Ideal A) (β : L →ₗ[A] T) :
    ∃ c : ℕ, ∀ n (x : L), β x ∈ I ^ (n + c) • (⊤ : Submodule A T) →
      ∃ y : LinearMap.ker β, x - y ∈ I ^ n • (⊤ : Submodule A L) := by
  obtain ⟨c, hc⟩ := exists_adic_smul_top_preimage I β
  refine ⟨c, fun n x hx => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hc n x hx
  exact ⟨⟨x - z, by simp [LinearMap.mem_ker, hzx]⟩, by simpa using hz⟩

private lemma exists_adic_injective_bound
    {A H L : Type*} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup H] [Module A H]
    [AddCommGroup L] [Module A L] [Module.Finite A L]
    (I : Ideal A) (f : H →ₗ[A] L) (hf : Function.Injective f) :
    ∃ c : ℕ, ∀ n (a : A), a ∈ I ^ c → ∀ x : H,
      f x ∈ I ^ n • (⊤ : Submodule A L) →
      a • x ∈ I ^ n • (⊤ : Submodule A H) := by
  obtain ⟨c, hc⟩ := exists_adic_smul_top_preimage I f
  refine ⟨c, fun n a ha x hx => ?_⟩
  obtain ⟨y, hy, he⟩ := hc n (a • x) (by
    rw [map_smul, Nat.add_comm, pow_add, mul_smul]
    exact Submodule.smul_mem_smul ha hx)
  exact hf he ▸ hy

private noncomputable def homRestriction
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k : ℕ} (h : n ≤ k) :
    ((M ⧸ I ^ k • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ k • (⊤ : Submodule A N))) →ₗ[A]
    ((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
  ((homSystem (M := M) (N := N) I).map (homOfLE h).op).hom

private lemma homRestriction_refl
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (q : (M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N))) :
    homRestriction I (le_refl n) q = q := by
  show ((homSystem (M := M) (N := N) I).map (𝟙 (op n))).hom q = q
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma homSystem_map_apply_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k : ℕ} (h : n ≤ k)
    (f : (M ⧸ I ^ k • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ k • (⊤ : Submodule A N))) (m : M) :
    homRestriction I h f (Submodule.Quotient.mk m) =
      AdicCompletion.transitionMap I N h (f (Submodule.Quotient.mk m)) := by
  induction k, h using Nat.le_induction with
  | base => simp [homRestriction_refl]
  | succ k h ih =>
    have he : (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [homRestriction, he, Functor.map_comp]
    simp only [homSystem, Functor.ofOpSequence_map_homOfLE_succ]
    show homRestriction I h (homTransition I k f)
      (Submodule.Quotient.mk m) = _
    rw [ih, homTransition_apply_mk]
    generalize f (Submodule.Quotient.mk m) = z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl

private lemma homSystem_map_comparison_mk
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k : ℕ} (h : n ≤ k) (f : M →ₗ[A] N) :
    homRestriction I h
      (comparison I k (Submodule.Quotient.mk f)) =
        comparison I n (Submodule.Quotient.mk f) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m => simp [homSystem_map_apply_mk, comparison_apply_mk]

private lemma presentation_hom_lift
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {G R : Type u} [Finite R]
    (f : (G →₀ A) →ₗ[A] M) (g : (R →₀ A) →ₗ[A] (G →₀ A))
    (hfg : Function.Exact g f) (J : Ideal A)
    (q : (M ⧸ J • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ J • (⊤ : Submodule A N))) :
    ∃ l : (G →₀ A) →ₗ[A] N,
      (J • (⊤ : Submodule A N)).mkQ.comp l = (homQuotientEquiv J q).comp f ∧
      l.comp g ∈ J • (⊤ : Submodule A ((R →₀ A) →ₗ[A] N)) := by
  obtain ⟨l, hl⟩ := finite_free_hom_reduce_surjective J ((homQuotientEquiv J q).comp f)
  refine ⟨l, hl, ?_⟩
  rw [finite_free_hom_mem_smul_iff, ← LinearMap.comp_assoc, hl, LinearMap.comp_assoc]
  have hzero : f.comp g = 0 := LinearMap.ext fun r => (hfg (g r)).2 ⟨r, rfl⟩
  rw [hzero, LinearMap.comp_zero]

private lemma presentation_hom_approximation
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {G : Type u} (f : (G →₀ A) →ₗ[A] M) (hf : Function.Surjective f)
    (I : Ideal A) {n k : ℕ} (hnk : n ≤ k)
    (q : (M ⧸ I ^ k • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ k • (⊤ : Submodule A N)))
    (l : (G →₀ A) →ₗ[A] N) (u : M →ₗ[A] N)
    (hl : (I ^ k • (⊤ : Submodule A N)).mkQ.comp l =
      (homQuotientEquiv (I ^ k) q).comp f)
    (hu : l - u.comp f ∈ I ^ n • (⊤ : Submodule A ((G →₀ A) →ₗ[A] N))) :
    homRestriction I hnk q =
      comparison I n (Submodule.Quotient.mk u) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
    obtain ⟨r, rfl⟩ := hf m
    rw [homSystem_map_apply_mk, comparison_apply_mk]
    have he : q (Submodule.Quotient.mk (f r)) = Submodule.Quotient.mk (l r) :=
      (LinearMap.congr_fun hl r).symm
    rw [he]
    show (Submodule.Quotient.mk (l r) : N ⧸ I ^ n • (⊤ : Submodule A N)) =
      Submodule.Quotient.mk (u (f r))
    exact (Submodule.Quotient.eq _).2
      (Submodule.smul_top_le_comap_smul_top (I ^ n) (LinearMap.applyₗ r) hu)

private lemma homSystem_uniform_approximation
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) :
    ∃ c : ℕ,
      (∀ n (q : (M ⧸ I ^ (n + c) • (⊤ : Submodule A M)) →ₗ[A]
          (N ⧸ I ^ (n + c) • (⊤ : Submodule A N))),
        ∃ u : M →ₗ[A] N,
          homRestriction I (Nat.le_add_right n c) q =
            comparison I n (Submodule.Quotient.mk u)) ∧
      (∀ n,
        I ^ c ≤ Module.annihilator A (LinearMap.ker (comparison (M := M) (N := N) I n)) ∧
        I ^ c ≤ Module.annihilator A
          (((M ⧸ I ^ n • (⊤ : Submodule A M)) →ₗ[A]
            (N ⧸ I ^ n • (⊤ : Submodule A N))) ⧸ LinearMap.range (comparison I n))) := by
  obtain ⟨G, R, hG, hR, f, g, hf, hfg⟩ := finite_presentation_finsupp (A := A) (M := M)
  let := hG
  let := hR
  let β := LinearMap.lcomp A N g
  let ι := LinearMap.lcomp A N f
  obtain ⟨hex, hinj⟩ := finite_presentation_hom_kernel (N := N) hf hfg
  obtain ⟨b, hb⟩ := exists_adic_preimage_bound I β
  obtain ⟨d, hd⟩ := exists_adic_injective_bound I ι hinj
  let c := b + d
  have hcb : I ^ c ≤ I ^ b := Ideal.pow_le_pow_right (by dsimp [c]; omega)
  have hcd : I ^ c ≤ I ^ d := Ideal.pow_le_pow_right (by dsimp [c]; omega)
  have descend (y : LinearMap.ker β) : ∃ u : M →ₗ[A] N, u.comp f = y :=
    (hex y).1 y.property
  refine ⟨c, ?_, ?_⟩
  · intro n q
    obtain ⟨l, hl, hlg⟩ := presentation_hom_lift f g hfg (I ^ (n + c)) q
    have hlg' : β l ∈ I ^ (n + b) • (⊤ : Submodule A ((R →₀ A) →ₗ[A] N)) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by dsimp [c]; omega))) hlg
    obtain ⟨y, hy⟩ := hb n l hlg'
    obtain ⟨u, hu⟩ := descend y
    refine ⟨u, presentation_hom_approximation f hf I (Nat.le_add_right n c) q l u hl ?_⟩
    rwa [hu]
  · intro n
    constructor
    · intro a ha
      rw [Module.mem_annihilator]
      intro z
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective
        (I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) z.1
      have hx0 : comparison I n (Submodule.Quotient.mk x) = 0 := by
        show comparison I n ((I ^ n • (⊤ : Submodule A (M →ₗ[A] N))).mkQ x) = 0
        rw [hx]
        exact z.property
      have hix : ι x ∈ I ^ n • (⊤ : Submodule A ((G →₀ A) →ₗ[A] N)) := by
        rw [finite_free_hom_mem_smul_iff]
        apply LinearMap.ext
        intro r
        have hz := LinearMap.congr_fun hx0 (Submodule.Quotient.mk (f r))
        simpa [comparison_apply_mk, ι] using hz
      apply Subtype.ext
      show a • z.1 = 0
      rw [← hx]
      show (Submodule.Quotient.mk (a • x) :
        (M →ₗ[A] N) ⧸ I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 (hd n a (hcd ha) x hix)
    · intro a ha
      rw [Module.mem_annihilator]
      intro z
      induction z using Submodule.Quotient.induction_on with
      | _ q =>
        obtain ⟨l, hl, hlg⟩ := presentation_hom_lift f g hfg (I ^ n) q
        have hlg' : β (a • l) ∈ I ^ (n + b) •
            (⊤ : Submodule A ((R →₀ A) →ₗ[A] N)) := by
          rw [map_smul, Nat.add_comm, pow_add, mul_smul]
          exact Submodule.smul_mem_smul (hcb ha) hlg
        obtain ⟨y, hy⟩ := hb n (a • l) hlg'
        obtain ⟨u, hu⟩ := descend y
        have hl' : (I ^ n • (⊤ : Submodule A N)).mkQ.comp (a • l) =
            (homQuotientEquiv (I ^ n) (a • q)).comp f := by
          apply LinearMap.ext
          intro r
          show (I ^ n • (⊤ : Submodule A N)).mkQ (a • l r) =
            (homQuotientEquiv (I ^ n) (a • q)) (f r)
          rw [map_smul, map_smul]
          exact congrArg (fun t => a • t) (LinearMap.congr_fun hl r)
        have he := presentation_hom_approximation f hf I (le_refl n) (a • q)
          (a • l) u hl' (by rwa [hu])
        have he' : comparison I n (Submodule.Quotient.mk u) = a • q := by
          rw [homRestriction_refl] at he
          exact he.symm
        show (Submodule.Quotient.mk (a • q) : _ ⧸ LinearMap.range (comparison I n)) = 0
        exact (Submodule.Quotient.mk_eq_zero _).2 ⟨Submodule.Quotient.mk u, he'⟩

private lemma homSystem_isMittagLeffler
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) :
    (homSystem (M := M) (N := N) I ⋙ forget (ModuleCat A)).IsMittagLeffler := by
  obtain ⟨c, hc, _⟩ := homSystem_uniform_approximation (M := M) (N := N) I
  intro j
  refine ⟨op (j.unop + c), (homOfLE (Nat.le_add_right j.unop c)).op, ?_⟩
  intro k h q hq
  obtain ⟨q, rfl⟩ := hq
  obtain ⟨u, hu⟩ := hc j.unop q
  refine ⟨comparison I k.unop (Submodule.Quotient.mk u), ?_⟩
  have he : h = (homOfLE (leOfHom h.unop)).op := Subsingleton.elim _ _
  rw [he]
  exact (homSystem_map_comparison_mk I _ u).trans hu.symm

private lemma sup_pow_smul_eq_top
    {A L : Type*} [CommRing A] [AddCommGroup L] [Module A L]
    (I : Ideal A) (P : Submodule A L)
    (h : P ⊔ I • (⊤ : Submodule A L) = ⊤) (n : ℕ) :
    P ⊔ I ^ n • (⊤ : Submodule A L) = ⊤ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      P ⊔ I ^ (n + 1) • (⊤ : Submodule A L) =
          (P ⊔ I ^ n • P) ⊔ I ^ n • (I • (⊤ : Submodule A L)) := by
            rw [show P ⊔ I ^ n • P = P from sup_eq_left.2 Submodule.smul_le_right,
              pow_succ, mul_smul]
      _ = P ⊔ I ^ n • (P ⊔ I • (⊤ : Submodule A L)) := by
        rw [Submodule.smul_sup, sup_assoc]
      _ = ⊤ := by rw [h, ih]

private lemma comparison_surjective_of_sub_mem
    {A : Type u} {M : Type v} [CommRing A]
    [AddCommGroup M] [Module A M]
    (I : Ideal A) (f : M →ₗ[A] M)
    (hf : ∀ x, f x - x ∈ I • (⊤ : Submodule A M)) (n : ℕ) :
    Function.Surjective (comparison I n (Submodule.Quotient.mk f)) := by
  have htop : LinearMap.range f ⊔ I • (⊤ : Submodule A M) = ⊤ := by
    apply top_unique
    intro x _
    have he : x = f x + (x - f x) := by abel
    rw [he]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ (by simpa using Submodule.neg_mem _ (hf x))
  have hn := sup_pow_smul_eq_top I (LinearMap.range f) htop n
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    have hx : x ∈ LinearMap.range f ⊔ I ^ n • (⊤ : Submodule A M) := by rw [hn]; trivial
    obtain ⟨y, ⟨z, rfl⟩, w, hw, he⟩ := Submodule.mem_sup.mp hx
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [comparison_apply_mk]
    exact (Submodule.Quotient.eq _).2 (by
      have hd : f z - x = -w := by rw [← he]; abel
      rw [hd]
      exact Submodule.neg_mem _ hw)

private lemma comparison_mk_comp
    {A : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P]
    (I : Ideal A) (n : ℕ) (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    comparison I n (Submodule.Quotient.mk (g.comp f)) =
      (comparison I n (Submodule.Quotient.mk g)).comp
        (comparison I n (Submodule.Quotient.mk f)) := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x => simp [comparison_apply_mk]

private lemma comparison_sub_mem_of_eq_id
    {A L : Type*} [CommRing A] [AddCommGroup L] [Module A L]
    (I : Ideal A) (t : L →ₗ[A] L) {m : ℕ} (hm : 0 < m)
    (ht : comparison I m (Submodule.Quotient.mk t) = LinearMap.id) :
    ∀ x, t x - x ∈ I • (⊤ : Submodule A L) := by
  intro x
  have he := LinearMap.congr_fun ht (Submodule.Quotient.mk x)
  rw [comparison_apply_mk] at he
  have hx : t x - x ∈ I ^ m • (⊤ : Submodule A L) :=
    (Submodule.Quotient.eq _).1 he
  exact (Submodule.smul_mono_left (show I ^ m ≤ I from
    by simpa using Ideal.pow_le_pow_right (I := I) (show 1 ≤ m by omega))) hx

private lemma comparison_bijective_of_inverse_mod
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) (f : M →ₗ[A] N) (g : N →ₗ[A] M)
    {m : ℕ} (hm : 0 < m)
    (hfg : comparison I m (Submodule.Quotient.mk (g.comp f)) = LinearMap.id)
    (hgf : comparison I m (Submodule.Quotient.mk (f.comp g)) = LinearMap.id)
    (n : ℕ) : Function.Bijective (comparison I n (Submodule.Quotient.mk f)) := by
  have hsurj₁ := comparison_surjective_of_sub_mem I (g.comp f)
    (comparison_sub_mem_of_eq_id I (g.comp f) hm hfg) n
  have hsurj₂ := comparison_surjective_of_sub_mem I (f.comp g)
    (comparison_sub_mem_of_eq_id I (f.comp g) hm hgf) n
  have hinj := IsNoetherian.injective_of_surjective_endomorphism
    (comparison I n (Submodule.Quotient.mk (g.comp f))) hsurj₁
  rw [comparison_mk_comp] at hinj hsurj₂
  exact ⟨Function.Injective.of_comp hinj, Function.Surjective.of_comp hsurj₂⟩

private lemma homRestriction_trans
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k l : ℕ} (hnk : n ≤ k) (hkl : k ≤ l)
    (q : (M ⧸ I ^ l • (⊤ : Submodule A M)) →ₗ[A]
      (N ⧸ I ^ l • (⊤ : Submodule A N))) :
    homRestriction I hnk (homRestriction I hkl q) =
      homRestriction I (hnk.trans hkl) q := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [homSystem_map_apply_mk, homSystem_map_apply_mk, homSystem_map_apply_mk]
    generalize q (Submodule.Quotient.mk x) = z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl

private noncomputable abbrev isoSystem
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) : ℕᵒᵖ ⥤ Type (max v w) :=
  Functor.ofOpSequence
    (X := fun n => (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N)))
    (fun n => TypeCat.ofHom (isoTransition I n))

private noncomputable def isoRestriction
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k : ℕ} (h : n ≤ k) :
    ((M ⧸ I ^ k • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ k • (⊤ : Submodule A N))) →
    ((M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N))) :=
  (isoSystem (M := M) (N := N) I).map (homOfLE h).op

private lemma isoRestriction_refl
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) (n : ℕ)
    (e : (M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ n • (⊤ : Submodule A N))) :
    isoRestriction I (le_refl n) e = e := by
  show ((isoSystem (M := M) (N := N) I).map (𝟙 (op n))) e = e
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma isoRestriction_toLinearMap
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k : ℕ} (h : n ≤ k)
    (e : (M ⧸ I ^ k • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ k • (⊤ : Submodule A N))) :
    (isoRestriction I h e).toLinearMap = homRestriction I h e.toLinearMap := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [homRestriction_refl]
    show ((isoSystem (M := M) (N := N) I).map (𝟙 (op n)) e).toLinearMap = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  | succ k h ih =>
    have he : (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [isoRestriction, homRestriction, he, Functor.map_comp, Functor.map_comp]
    simp only [isoSystem, homSystem, Functor.ofOpSequence_map_homOfLE_succ]
    exact ih (isoTransition I k e)

private lemma isoRestriction_symm
    {A : Type u} {M : Type v} {N : Type w} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (I : Ideal A) {n k : ℕ} (h : n ≤ k)
    (e : (M ⧸ I ^ k • (⊤ : Submodule A M)) ≃ₗ[A]
      (N ⧸ I ^ k • (⊤ : Submodule A N))) :
    isoRestriction I h e.symm = (isoRestriction I h e).symm := by
  induction k, h using Nat.le_induction with
  | base => simp only [isoRestriction_refl]
  | succ k h ih =>
    have he : (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    simp only [isoRestriction, he, Functor.map_comp, isoSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    show isoRestriction I h (isoTransition I k e.symm) =
      (isoRestriction I h (isoTransition I k e)).symm
    rw [isoTransition_symm, ih]

private lemma isoSystem_isMittagLeffler
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) : (isoSystem (M := M) (N := N) I).IsMittagLeffler := by
  obtain ⟨c, hc, _⟩ := homSystem_uniform_approximation (M := M) (N := N) I
  obtain ⟨d, hd, _⟩ := homSystem_uniform_approximation (M := N) (N := M) I
  intro j
  let m := j.unop + 1
  let r := m + c + d
  have hjm : j.unop ≤ m := by dsimp [m]; omega
  have hmr : m ≤ r := by dsimp [r]; omega
  have hjr : j.unop ≤ r := hjm.trans hmr
  refine ⟨op r, (homOfLE hjr).op, ?_⟩
  intro k h z hz
  obtain ⟨e, rfl⟩ := hz
  change (M ⧸ I ^ r • (⊤ : Submodule A M)) ≃ₗ[A]
    (N ⧸ I ^ r • (⊤ : Submodule A N)) at e
  have hcr : m + c ≤ r := by dsimp [r]; omega
  have hdr : m + d ≤ r := by dsimp [r]; omega
  obtain ⟨f, hf⟩ := hc m (homRestriction I hcr e.toLinearMap)
  obtain ⟨g, hg⟩ := hd m (homRestriction I hdr e.symm.toLinearMap)
  rw [homRestriction_trans] at hf hg
  let em := isoRestriction I hmr e
  have hf' : comparison I m (Submodule.Quotient.mk f) = em.toLinearMap :=
    hf.symm.trans (isoRestriction_toLinearMap I hmr e).symm
  have hg' : comparison I m (Submodule.Quotient.mk g) = em.symm.toLinearMap := by
    show comparison I m (Submodule.Quotient.mk g) =
      (isoRestriction I hmr e).symm.toLinearMap
    rw [← isoRestriction_symm]
    exact hg.symm.trans (isoRestriction_toLinearMap I hmr e.symm).symm
  have hfg : comparison I m (Submodule.Quotient.mk (g.comp f)) = LinearMap.id := by
    rw [comparison_mk_comp, hf', hg']
    exact em.symm_comp
  have hgf : comparison I m (Submodule.Quotient.mk (f.comp g)) = LinearMap.id := by
    rw [comparison_mk_comp, hf', hg']
    exact em.comp_symm
  let ek := LinearEquiv.ofBijective (comparison I k.unop (Submodule.Quotient.mk f))
    (comparison_bijective_of_inverse_mod I f g (by dsimp [m]; omega) hfg hgf k.unop)
  refine ⟨ek, ?_⟩
  have he : h = (homOfLE (leOfHom h.unop)).op := Subsingleton.elim _ _
  rw [he]
  show isoRestriction I (leOfHom h.unop) ek = isoRestriction I hjr e
  apply LinearEquiv.toLinearMap_injective
  rw [isoRestriction_toLinearMap, isoRestriction_toLinearMap]
  show homRestriction I (leOfHom h.unop)
    (comparison I k.unop (Submodule.Quotient.mk f)) = homRestriction I hjr e.toLinearMap
  rw [homSystem_map_comparison_mk]
  rw [← homRestriction_trans I hjm hmr, hf, homSystem_map_comparison_mk]

/-- **Stacks 09BB.** Homomorphisms and isomorphisms between the adic quotients of two
finite modules form Mittag--Leffler systems.  The canonical comparison from the adic
quotients of `Hom` has uniformly bounded kernel and cokernel, and passage to the inverse
limit identifies both homomorphisms and isomorphisms with those between the completed
modules. -/
@[stacks 09BB, ega "0 7.3.4" "Hom^ ≅ Hom(M^,N^)", ega "0 7.8.2" "canonical isomorphism"]
public theorem hom_isom_quotient_systems_mittagLeffler_and_completion
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A) :
    let Mq : ℕ → Type _ := fun n => M ⧸ I ^ n • (⊤ : Submodule A M)
    let Nq : ℕ → Type _ := fun n => N ⧸ I ^ n • (⊤ : Submodule A N)
    let H : ℕ → Type _ := fun n => Mq n →ₗ[A] Nq n
    let E : ℕ → Type _ := fun n => Mq n ≃ₗ[A] Nq n
    ∃ (homTransition : ∀ n, H (n + 1) →ₗ[A] H n)
      (isoTransition : ∀ n, E (n + 1) → E n)
      (comparison : ∀ n,
        ((M →ₗ[A] N) ⧸ I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) →ₗ[A] H n),
      (∀ n (f : H (n + 1)) (m : M),
        homTransition n f (Submodule.Quotient.mk m) =
          AdicCompletion.transitionMap I N (Nat.le_succ n)
            (f (Submodule.Quotient.mk m))) ∧
      (∀ n (e : E (n + 1)) (m : M),
        isoTransition n e (Submodule.Quotient.mk m) =
          AdicCompletion.transitionMap I N (Nat.le_succ n)
            (e (Submodule.Quotient.mk m))) ∧
      (∀ n (f : M →ₗ[A] N) (m : M),
        comparison n (Submodule.Quotient.mk f) (Submodule.Quotient.mk m) =
          Submodule.Quotient.mk (f m)) ∧
      let HomSys : ℕᵒᵖ ⥤ ModuleCat A :=
        Functor.ofOpSequence (X := fun n => ModuleCat.of A (H n))
          (fun n => ModuleCat.ofHom (homTransition n))
      let IsoSys : ℕᵒᵖ ⥤ Type (max v w) :=
        Functor.ofOpSequence (X := E) (fun n => TypeCat.ofHom (isoTransition n))
      (HomSys ⋙ forget (ModuleCat A)).IsMittagLeffler ∧
      IsoSys.IsMittagLeffler ∧
      (∃ c : ℕ, ∀ n,
        I ^ c ≤ Module.annihilator A (LinearMap.ker (comparison n)) ∧
        I ^ c ≤ Module.annihilator A
          (H n ⧸ LinearMap.range (comparison n))) ∧
      (∃ homLimitIso :
          limit HomSys ≅ ModuleCat.of A (AdicCompletion I (M →ₗ[A] N)),
        ∀ (f : ↥(limit HomSys)) n,
          comparison n
              (AdicCompletion.eval I (M →ₗ[A] N) n (homLimitIso.hom.hom f)) =
            (limit.π HomSys (op n)).hom f) ∧
      (∃ completedHomEquiv :
          AdicCompletion I (M →ₗ[A] N) ≃ₗ[AdicCompletion I A]
            (AdicCompletion I M →ₗ[AdicCompletion I A] AdicCompletion I N),
        ∀ (f : M →ₗ[A] N) (m : M),
          completedHomEquiv (AdicCompletion.of I (M →ₗ[A] N) f)
              (AdicCompletion.of I M m) =
            AdicCompletion.of I N (f m)) ∧
      ∃ isoLimitEquiv :
          { e : ∀ n, E n // ∀ n, isoTransition n (e (n + 1)) = e n } ≃
            (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N),
        ∀ (e : { e : ∀ n, E n // ∀ n, isoTransition n (e (n + 1)) = e n })
          (n : ℕ) (m : M),
          e.1 n (Submodule.Quotient.mk m) =
            AdicCompletion.eval I N n
              (isoLimitEquiv e (AdicCompletion.of I M m)) := by
  dsimp only
  refine ⟨homTransition I, isoTransition I, comparison I,
    homTransition_apply_mk I, isoTransition_apply_mk I, comparison_apply_mk I, ?_⟩
  refine ⟨homSystem_isMittagLeffler I, isoSystem_isMittagLeffler I, ?_, ?_, ?_, ?_⟩
  · obtain ⟨c, _, hc⟩ := homSystem_uniform_approximation (M := M) (N := N) I
    exact ⟨c, hc⟩
  · exact ⟨homLimitIso I, homLimitIso_projection I⟩
  · exact ⟨completedHomEquivGeneral I, completedHomEquivGeneral_of_apply I⟩
  · exact ⟨isoLimitEquiv I, fun _ _ _ => rfl⟩

end Stacks.AdicSystem.HomComparison

end

/-! ## Tag 09BC -/

section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.AdicSystem.CompletionIsomorphism

universe u v w

/-- **Stacks 09BC.** If all quotients of two finite modules by powers of an ideal
are linearly equivalent, then their adic completions are linearly equivalent over
the completed ring. -/
@[stacks 09BC]
public theorem adicCompletion_linearEquiv_of_quotient_linearEquiv
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I : Ideal A)
    (h : ∀ n : ℕ,
      Nonempty ((M ⧸ I ^ n • (⊤ : Submodule A M)) ≃ₗ[A]
        (N ⧸ I ^ n • (⊤ : Submodule A N)))) :
    Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := by
  obtain ⟨homTransition, isoTransition, comparison, -, -, -, -, hML, -, -, -, isoLimitEquiv, -⟩ :=
    Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion
      (A := A) (M := M) (N := N) I
  obtain ⟨s⟩ := nonempty_sections_of_isMittagLeffler hML (fun ⟨n⟩ ↦ h n)
  apply Nonempty.map isoLimitEquiv
  exact ⟨fun n ↦ s.val (op n), fun n ↦ by
    have hs := s.property (homOfLE (Nat.le_succ n)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at hs
    change isoTransition n (s.val (op (n + 1))) = s.val (op n) at hs
    exact hs⟩

end Stacks.AdicSystem.CompletionIsomorphism

end

end