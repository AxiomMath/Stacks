module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Warfield

/-!
# Generalized valuation rings

A nonzero commutative ring is a *generalized valuation ring* when divisibility of its elements is
total; equivalently, when it is local and every finitely generated ideal is principal;
equivalently, when its ideals are totally ordered by inclusion. Over such a ring every finitely
presented module is a finite direct sum of cyclic modules `R ⧸ (f)`. More generally, if the
localization of `R` at every maximal ideal is Bézout, then every finitely presented `R`-module is
a direct summand of a finite direct sum of such cyclic modules.

## Main results

* `generalizedValuationRing_tfae`: the three characterizations of a generalized valuation ring,
  together with the valuation-ring special case.
* `finitePresentation_equiv_directSum_quotient_span_singleton`: a finitely presented module over a
  local Bézout ring is isomorphic to a finite direct sum of modules `R ⧸ (f)`.
* `finitePresentation_summand_fin_directSum_quotient_span_singleton`: a finitely presented module
  over a ring that is Bézout locally at every maximal ideal is a direct summand of a finite direct
  sum of modules `R ⧸ (f)`.

## References

* [Stacks, Tag 0ASN](https://stacks.math.columbia.edu/tag/0ASN)
* [Stacks, Tag 0ASP](https://stacks.math.columbia.edu/tag/0ASP)
* [Stacks, Tag 0ASQ](https://stacks.math.columbia.edu/tag/0ASQ)
-/

@[expose] public section

open scoped DirectSum
open Pointwise

universe u v w x y

/-! ### Generalized valuation rings -/

private theorem total_dvd_iff_local_bezout (R : Type u) [CommRing R] [Nontrivial R] :
    @Std.Total R (· ∣ ·) ↔ IsBezout R ∧ IsLocalRing R := by
  rw [← PreValuationRing.iff_dvd_total]
  constructor
  · intro h
    let _ : PreValuationRing R := h
    refine ⟨?_, inferInstance⟩
    rw [IsBezout.iff_span_pair_isPrincipal]
    intro x y
    rcases (PreValuationRing.iff_ideal_total.mp h).total
        (Ideal.span {x}) (Ideal.span {y}) with hxy | hyx
    · rw [Ideal.span_insert, sup_eq_right.mpr hxy]
      exact ⟨⟨y, rfl⟩⟩
    · rw [Ideal.span_insert, sup_eq_left.mpr hyx]
      exact ⟨⟨x, rfl⟩⟩
  · rintro ⟨hbezout, hlocal⟩
    let _ : IsBezout R := hbezout
    let _ : IsLocalRing R := hlocal
    rw [PreValuationRing.iff_dvd_total]
    refine ⟨fun a b => ?_⟩
    obtain ⟨g, e : _ = Ideal.span _⟩ := IsBezout.span_pair_isPrincipal a b
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp
        (show a ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp
        (show b ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
    obtain ⟨x, y, e'⟩ := Ideal.mem_span_pair.mp
        (show g ∈ Ideal.span {a * g, b * g} by rw [e]; exact Ideal.subset_span (by simp))
    rcases eq_or_ne g 0 with hg | hg
    · simp [hg]
    have hprod : (x * a + y * b) * g = g := by
      calc
        (x * a + y * b) * g = x * (a * g) + y * (b * g) := by ring
        _ = g := e'
    have hnonunit : ¬ IsUnit (1 - (x * a + y * b)) := by
      rintro ⟨u, hu⟩
      have hz : (u : R) * g = 0 := by rw [hu, sub_mul, one_mul, hprod, sub_self]
      apply hg
      calc
        g = (↑(u⁻¹) : R) * ((u : R) * g) := by simp
        _ = 0 := by rw [hz, mul_zero]
    have hsum : IsUnit (x * a + y * b) :=
      (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right hnonunit
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hx | hy
    · exact .inl <| mul_dvd_mul_right (isUnit_iff_forall_dvd.mp (isUnit_of_mul_isUnit_right hx) b) g
    · exact .inr <| mul_dvd_mul_right (isUnit_iff_forall_dvd.mp (isUnit_of_mul_isUnit_right hy) a) g

/-- For a nonzero commutative ring, total divisibility, being a local Bézout ring, and total
inclusion of ideals are equivalent. In particular, all three properties hold for a valuation
ring. -/
@[stacks 0ASN]
theorem generalizedValuationRing_tfae (R : Type u) [CommRing R] [Nontrivial R] :
    List.TFAE
        [@Std.Total R (· ∣ ·),
          IsBezout R ∧ IsLocalRing R,
          @Std.Total (Ideal R) (· ≤ ·)] ∧
      (∀ [IsDomain R] [ValuationRing R],
        @Std.Total R (· ∣ ·) ∧
          (IsBezout R ∧ IsLocalRing R) ∧
          @Std.Total (Ideal R) (· ≤ ·)) := by
  constructor
  · tfae_have 1 ↔ 2 := total_dvd_iff_local_bezout R
    tfae_have 1 ↔ 3 :=
      PreValuationRing.iff_dvd_total.symm.trans PreValuationRing.iff_ideal_total
    tfae_finish
  · intro _ _
    have hdvd : @Std.Total R (· ∣ ·) := ValuationRing.iff_dvd_total.mp (inferInstance)
    exact ⟨hdvd, ⟨inferInstance, inferInstance⟩,
      PreValuationRing.iff_ideal_total.mp
        (PreValuationRing.iff_dvd_total.mpr hdvd)⟩

/-! ### Finitely presented modules over a local Bézout ring -/

private theorem preValuationRing (R : Type*) [CommRing R] [IsBezout R] [IsLocalRing R] :
    PreValuationRing R := by
  apply PreValuationRing.iff_ideal_total.mpr
  exact ((generalizedValuationRing_tfae R).1.out 2 3).mp
    (show IsBezout R ∧ IsLocalRing R from ⟨inferInstance, inferInstance⟩)

private theorem span_eq_top_of_perturb {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ι : Type*} (x y : ι → M)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hxy : ∀ i, x i - y i ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    Submodule.span R (Set.range y) = ⊤ := by
  let N : Submodule R M := Submodule.span R (Set.range y)
  have h : (⊤ : Submodule R M) ≤ N ⊔ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
    nth_rewrite 1 [← hx]
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    have hyi : y i ∈ N := Submodule.subset_span ⟨i, rfl⟩
    have hxi : x i = y i + (x i - y i) := by abel
    rw [hxi]
    exact (N ⊔ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).add_mem
      (Submodule.mem_sup_left hyi) (Submodule.mem_sup_right (hxy i))
  exact top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) h)

private theorem exists_generator_stable_ann {R : Type*} [CommRing R] [IsBezout R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {ι : Type*} [Finite ι] [Nonempty ι]
    (x : ι → M) (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ i : ι, ∀ y : M,
      x i - y ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) →
        (R ∙ y).annihilator = Module.annihilator R M := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : PreValuationRing R := preValuationRing R
  let : DecidableLE (Ideal R) := Classical.decRel (· ≤ ·)
  let : LinearOrder (Ideal R) := ValuationRing.instLinearOrderIdealOfDecidableLE R
  by_contra h
  push Not at h
  choose y hy hyne using h
  have hyspan : Submodule.span R (Set.range y) = ⊤ :=
    span_eq_top_of_perturb x y hx hy
  let A : ι → Ideal R := fun i ↦ (R ∙ y i).annihilator
  let S : Finset (Ideal R) := Finset.univ.image A
  have hS : S.Nonempty := Finset.univ_nonempty.image A
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  have hmin : ∀ j, A i ≤ A j := by
    intro j
    rw [hi]
    exact S.min'_le _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hle : Module.annihilator R M ≤ A i := by
    intro r hr
    exact (Submodule.mem_annihilator_span_singleton (y i) r).mpr
      ((Module.mem_annihilator).mp hr (y i))
  have hge : A i ≤ Module.annihilator R M := by
    intro r hr
    have hkill : ∀ j, r • y j = 0 := fun j =>
      (Submodule.mem_annihilator_span_singleton (y j) r).mp (hmin j hr)
    have hz : r ∈ (Submodule.span R (Set.range y)).annihilator := by
      apply (Submodule.mem_annihilator_span (Set.range y) r).mpr
      rintro ⟨z, ⟨j, rfl⟩⟩
      exact hkill j
    rw [hyspan] at hz
    exact (Module.mem_annihilator).mpr (fun m ↦
      (Submodule.mem_annihilator (N := (⊤ : Submodule R M))).mp hz m (Submodule.mem_top))
  exact hyne i (le_antisymm hge hle)

/-- A cyclic submodule generated by an element whose annihilator is stable under perturbation by
the maximal ideal is a pure submodule. -/
private theorem span_singleton_pure {R : Type*} [CommRing R] [IsBezout R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] (x : M)
    (hstable : ∀ y : M,
      x - y ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) →
        (R ∙ y).annihilator = Module.annihilator R M) (f : R) :
    f • (R ∙ x) = (R ∙ x) ⊓ f • (⊤ : Submodule R M) := by
  classical
  let : PreValuationRing R := preValuationRing R
  ext m
  constructor
  · intro hm
    obtain ⟨a, ha, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists m f (R ∙ x)).mp hm
    exact ⟨(R ∙ x).smul_mem f ha,
      Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_top)⟩
  · intro hm
    obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hm.1
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists m f ⊤).mp hm.2
    have hgy : g • x = f • y := hg.trans hy.symm
    by_cases hfg : f ∣ g
    · obtain ⟨c, rfl⟩ := hfg
      apply (Submodule.mem_smul_pointwise_iff_exists m f (R ∙ x)).mpr
      refine ⟨c • x, (R ∙ x).smul_mem c (Submodule.mem_span_singleton_self x), ?_⟩
      simpa [smul_smul] using hg
    · obtain ⟨h, hgh⟩ := (ValuationRing.dvd_total f g).resolve_left hfg
      have hh : h ∈ IsLocalRing.maximalIdeal R := by
        by_contra hh
        have hu : IsUnit h := IsLocalRing.notMem_maximalIdeal.mp hh
        obtain ⟨u, rfl⟩ := hu
        apply hfg
        refine ⟨↑u⁻¹, ?_⟩
        rw [hgh]
        simp [mul_assoc]
      have hpert : x - (x - h • y) ∈ IsLocalRing.maximalIdeal R •
          (⊤ : Submodule R M) := by
        simpa using (Submodule.smul_mem_smul hh (Submodule.mem_top : y ∈ (⊤ : Submodule R M)))
      have hzero : g • (x - h • y) = 0 := by
        rwa [smul_sub, smul_smul, ← hgh, sub_eq_zero]
      have hmem : g ∈ Module.annihilator R M := by
        rw [← hstable _ hpert]
        exact (Submodule.mem_annihilator_span_singleton _ _).mpr hzero
      rw [← hg, Module.mem_annihilator.mp hmem x]
      exact (f • (R ∙ x)).zero_mem

/-- A map from a module isomorphic to a finite direct sum of cyclic modules `R ⧸ (f)` into the
target `C` of a surjection `β` with pure kernel lifts along `β`. -/
private theorem exists_lift_of_equiv_directSum_quotient {R : Type u} [CommRing R] {n : ℕ}
    (fs : Fin n → R) {N : Type v} {A : Type w} {B : Type x} {C : Type y}
    [AddCommGroup N] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R N] [Module R A] [Module R B] [Module R C]
    (e : N ≃ₗ[R] ⨁ i : Fin n, R ⧸ Ideal.span {fs i})
    (α : A →ₗ[R] B) (β : B →ₗ[R] C) (hβ : Function.Surjective β)
    (hrk : LinearMap.range α = LinearMap.ker β)
    (hpure : ∀ f : R,
      f • LinearMap.range α = LinearMap.range α ⊓ f • (⊤ : Submodule R B))
    (ψ : N →ₗ[R] C) : ∃ Φ : N →ₗ[R] B, β ∘ₗ Φ = ψ := by
  obtain ⟨Φ, hΦ⟩ := directSum_cyclic_lifts fs α β hβ hrk hpure (ψ ∘ₗ e.symm.toLinearMap)
  exact ⟨Φ ∘ₗ e.toLinearMap, by
    rw [← LinearMap.comp_assoc, hΦ, LinearMap.comp_assoc, LinearEquiv.symm_comp,
      LinearMap.comp_id]⟩

/-- If a submodule `A ⊆ M` is pure and the quotient `M ⧸ A` is a finite direct sum of cyclic
modules `R ⧸ (f)`, then the quotient map `M → M ⧸ A` admits a linear section. -/
private theorem split_pure_extension {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (A : Submodule R M)
    (hpure : ∀ f : R, f • A = A ⊓ f • (⊤ : Submodule R M))
    {n : ℕ} (fs : Fin n → R)
    (e : (M ⧸ A) ≃ₗ[R] (⨁ i : Fin n, R ⧸ Ideal.span {fs i})) :
    ∃ s : (M ⧸ A) →ₗ[R] M, A.mkQ ∘ₗ s = LinearMap.id :=
  exists_lift_of_equiv_directSum_quotient fs e A.subtype A.mkQ A.mkQ_surjective (by simp)
    (by simpa only [Submodule.range_subtype] using hpure) LinearMap.id

private theorem cyclic_span_equiv_principal_quotient {R : Type*} [CommRing R]
    [IsBezout R] {M : Type*} [AddCommGroup M] [Module R M]
    (x : M) [Module.FinitePresentation R ↥(R ∙ x)] :
    ∃ f : R, Nonempty (↥(R ∙ x) ≃ₗ[R] R ⧸ Ideal.span {f}) := by
  let I := Ideal.torsionOf R M x
  let e : (R ⧸ I) ≃ₗ[R] ↥(R ∙ x) := Ideal.quotTorsionOfEquivSpanSingleton R M x
  let : Module.FinitePresentation R (R ⧸ I) :=
    Module.FinitePresentation.of_equiv e.symm
  have hfg : I.FG := by
    show Submodule.FG I
    simpa using Module.FinitePresentation.fg_ker (I.mkQ : R →ₗ[R] R ⧸ I) I.mkQ_surjective
  obtain ⟨f, hf⟩ := (IsBezout.isPrincipal_of_FG I hfg).1
  exact ⟨f, ⟨e.symm ≪≫ₗ Submodule.quotEquivOfEq I (Ideal.span {f}) hf⟩⟩

private theorem quotient_span_generators {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (x : Fin (n + 1) → M) (hx : Submodule.span R (Set.range x) = ⊤)
    (i : Fin (n + 1)) :
    Submodule.span R (Set.range (fun j : Fin n ↦
      (R ∙ x i).mkQ (x ((finSuccAboveEquiv i j).val)))) = ⊤ := by
  let A : Submodule R M := R ∙ x i
  let q := A.mkQ
  let y : Fin n → M ⧸ A := fun j ↦ q (x ((finSuccAboveEquiv i j).val))
  have hall : Submodule.span R (Set.range (fun k ↦ q (x k))) = ⊤ := by
    have hmap := LinearMap.map_span q (Set.range x)
    have hrange : q '' Set.range x = Set.range (fun k ↦ q (x k)) := by
      ext z
      simp
    rw [hrange, hx] at hmap
    rw [← hmap]
    simpa using (LinearMap.range_eq_top.mpr A.mkQ_surjective : q.range = ⊤)
  have hle : Submodule.span R (Set.range (fun k ↦ q (x k))) ≤
      Submodule.span R (Set.range y) := by
    apply Submodule.span_le.mpr
    rintro z ⟨k, rfl⟩
    by_cases hki : k = i
    · subst k
      have hz : q (x i) = 0 :=
        (Submodule.Quotient.mk_eq_zero A).mpr (Submodule.mem_span_singleton_self _)
      show q (x i) ∈ Submodule.span R (Set.range y)
      rw [hz]
      exact (Submodule.span R (Set.range y)).zero_mem
    · let j : Fin n := (finSuccAboveEquiv i).symm ⟨k, hki⟩
      have hj : (finSuccAboveEquiv i j).val = k := by
        simp [j]
      have : q (x k) = y j := by simp [y, hj]
      show q (x k) ∈ Submodule.span R (Set.range y)
      rw [this]
      exact Submodule.subset_span ⟨j, rfl⟩
  exact top_unique (hall ▸ hle)

private theorem product_equiv_directSum_succ {R : Type*} [CommRing R]
    {A : Type*} [AddCommGroup A] [Module R A]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    {M : Type*} [AddCommGroup M] [Module R M]
    (eP : (A × Q) ≃ₗ[R] M) (f : R)
    (eA : A ≃ₗ[R] R ⧸ Ideal.span {f})
    {n : ℕ} (fs : Fin n → R)
    (eQ : Q ≃ₗ[R] ⨁ j : Fin n, R ⧸ Ideal.span {fs j}) :
    ∃ gs : Fin (n + 1) → R,
      Nonempty (M ≃ₗ[R] ⨁ j : Fin (n + 1), R ⧸ Ideal.span {gs j}) := by
  let α : Option (Fin n) → Type _ := fun j ↦
    match j with
    | none => R ⧸ Ideal.span {f}
    | some k => R ⧸ Ideal.span {fs k}
  let : (j : Option (Fin n)) → AddCommMonoid (α j) := by
    intro j
    cases j <;> dsimp [α] <;> infer_instance
  let : (j : Option (Fin n)) → Module R (α j) := by
    intro j
    cases j <;> dsimp [α] <;> infer_instance
  let gs : Fin (n + 1) → R := fun j ↦
    match (finSuccEquiv n).symm.symm j with
    | none => f
    | some k => fs k
  let e : M ≃ₗ[R] ⨁ j : Option (Fin n), α j :=
    eP.symm ≪≫ₗ eA.prodCongr eQ ≪≫ₗ
      (DirectSum.lequivProdDirectSum R (α := α)).symm
  refine ⟨gs, ⟨e ≪≫ₗ ?_⟩⟩
  let eOption : (k : Option (Fin n)) →
      α k ≃ₗ[R] R ⧸ Ideal.span {match k with | none => f | some j => fs j} := by
    intro k
    cases k with
    | none => exact LinearEquiv.refl R _
    | some j => exact LinearEquiv.refl R _
  let ePoint : (j : Fin (n + 1)) →
      α ((finSuccEquiv n).symm.symm j) ≃ₗ[R] R ⧸ Ideal.span {gs j} :=
    fun j ↦ eOption ((finSuccEquiv n).symm.symm j)
  exact (DirectSum.lequivCongrLeft R (M := α) (finSuccEquiv n).symm) ≪≫ₗ
    DirectSum.congrLinearEquiv ePoint

/-- A finitely presented module over a local Bézout ring that is generated by `n` elements is a
finite direct sum of cyclic modules `R ⧸ (f)`. -/
private theorem decomposition_of_generators (R : Type u) [CommRing R]
    [IsBezout R] [IsLocalRing R] :
    ∀ n (M : Type w) [AddCommGroup M] [Module R M]
      [Module.FinitePresentation R M] (x : Fin n → M),
      Submodule.span R (Set.range x) = ⊤ →
        ∃ (k : ℕ) (fs : Fin k → R),
          Nonempty (M ≃ₗ[R] ⨁ j : Fin k, R ⧸ Ideal.span {fs j}) := by
  intro n
  induction n with
  | zero =>
      intro M _ _ _ x hx
      have hbot : (⊤ : Submodule R M) = ⊥ := by
        simpa using hx.symm
      have hzero : ∀ m : M, m = 0 := fun m =>
        (Submodule.eq_bot_iff (⊤ : Submodule R M)).mp hbot m Submodule.mem_top
      let : Subsingleton M := ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩
      exact ⟨0, isEmptyElim, ⟨LinearEquiv.ofSubsingleton M _⟩⟩
  | succ n ih =>
      intro M _ _ _ x hx
      obtain ⟨i, hstable⟩ := exists_generator_stable_ann x hx
      let A : Submodule R M := R ∙ x i
      have hfg : A.FG := Submodule.fg_span_singleton (x i)
      let : Module.FinitePresentation R (M ⧸ A) :=
        Module.finitePresentation_of_surjective A.mkQ A.mkQ_surjective
          (by simpa using hfg)
      let xq : Fin n → M ⧸ A := fun j ↦
        A.mkQ (x ((finSuccAboveEquiv i j).val))
      have hxq : Submodule.span R (Set.range xq) = ⊤ :=
        quotient_span_generators x hx i
      obtain ⟨k, fs, ⟨eQ⟩⟩ := ih (M ⧸ A) xq hxq
      obtain ⟨s, hs⟩ := split_pure_extension A (span_singleton_pure (x i) hstable) fs eQ
      let : Module.FinitePresentation R A :=
        Module.finitePresentation_of_split_exact A.subtype A.mkQ s hs
          A.subtype_injective (LinearMap.exact_subtype_mkQ A)
      obtain ⟨f, ⟨eA⟩⟩ := cyclic_span_equiv_principal_quotient (R := R) (M := M) (x i)
      have hexact : A.subtype.range = A.mkQ.ker := by
        simp
      let eP : (A × (M ⧸ A)) ≃ₗ[R] M :=
        lequivProdOfRightSplitExact A.subtype_injective hexact hs
      exact ⟨k + 1, product_equiv_directSum_succ eP f eA fs eQ⟩

/-- Every finitely presented module over a local Bézout ring is isomorphic to a finite direct
sum of quotients by principal ideals. -/
@[stacks 0ASP]
theorem finitePresentation_equiv_directSum_quotient_span_singleton
    (R : Type u) [CommRing R] [IsBezout R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ (n : ℕ) (f : Fin n → R),
      Nonempty (M ≃ₗ[R] ⨁ i : Fin n, R ⧸ Ideal.span {f i}) := by
  obtain ⟨n, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := M)
  exact decomposition_of_generators R n M x hx

/-! ### Finitely presented modules over a ring that is locally Bézout -/

private lemma localized_pointwise_smul {R : Type u} [CommRing R]
    (S : Submonoid R) {B : Type v} [AddCommGroup B] [Module R B]
    (N : Submodule R B) (f : R) :
    (f • N).localized S = (algebraMap R (Localization S) f) • N.localized S := by
  rw [← Submodule.ideal_span_singleton_smul]
  show (Ideal.span {f} • N).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S B) =
    (algebraMap R (Localization S) f) • N.localized S
  rw [Submodule.localized'_smul, Submodule.localized'_span]
  simp only [Set.image_singleton]
  rw [Submodule.ideal_span_singleton_smul]
  simp only [Algebra.linearMap_apply]

private lemma localized_pure {R : Type u} [CommRing R]
    (S : Submonoid R) {B : Type v} [AddCommGroup B] [Module R B]
    (N : Submodule R B)
    (hN : ∀ f : R, f • N = N ⊓ f • (⊤ : Submodule R B)) :
    ∀ f : Localization S,
      f • N.localized S = N.localized S ⊓
        f • (⊤ : Submodule (Localization S) (LocalizedModule S B)) := by
  intro f
  obtain ⟨r, s, hfs⟩ := IsLocalization.exists_mk'_eq S f
  rw [← hfs, IsLocalization.mk'_eq_mul_mk'_one]
  have hs : IsUnit (IsLocalization.mk' (Localization S) (1 : R) s) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨algebraMap R (Localization S) s, ?_⟩
    simpa only [IsLocalization.mk'_one, Submonoid.coe_one] using
      (IsLocalization.mk'_mul_mk'_eq_one (S := Localization S) (1 : S) s)
  simp only [mul_smul, Submodule.smul_eq_self_of_isUnit hs]
  rw [← localized_pointwise_smul S N r, hN r]
  show (N ⊓ r • (⊤ : Submodule R B)).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S B) = _
  rw [Submodule.localized'_inf]
  show N.localized S ⊓ (r • (⊤ : Submodule R B)).localized S = _
  rw [localized_pointwise_smul]
  show N.localized S ⊓ (algebraMap R (Localization S)) r •
      (⊤ : Submodule R B).localized' (Localization S) S
        (LocalizedModule.mkLinearMap S B) = _
  rw [Submodule.localized'_top]

private lemma localized_ker_pure {R : Type u} [CommRing R]
    (S : Submonoid R) {B : Type v} {C : Type w}
    [AddCommGroup B] [AddCommGroup C] [Module R B] [Module R C]
    (β : B →ₗ[R] C)
    (hpure : ∀ f : R,
      f • β.ker = β.ker ⊓ f • (⊤ : Submodule R B)) :
    ∀ f : Localization S,
      f • (LocalizedModule.map S β).ker =
        (LocalizedModule.map S β).ker ⊓
          f • (⊤ : Submodule (Localization S) (LocalizedModule S B)) := by
  have hker : (LocalizedModule.map S β).ker = β.ker.localized S := by
    apply Submodule.restrictScalars_injective R
    exact LinearMap.ker_localizedMap_eq_localized₀_ker S
      (LocalizedModule.mkLinearMap S B) (LocalizedModule.mkLinearMap S C) β
  rw [hker]
  exact localized_pure S β.ker hpure

private lemma localized_lift {R : Type u} [CommRing R]
    (S : Submonoid R) [IsBezout (Localization S)] [IsLocalRing (Localization S)]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {B : Type w} {C : Type x} [AddCommGroup B] [AddCommGroup C]
    [Module R B] [Module R C] (β : B →ₗ[R] C)
    (hβ : Function.Surjective β)
    (hpure : ∀ f : R,
      f • β.ker = β.ker ⊓ f • (⊤ : Submodule R B)) :
    Function.Surjective
      (fun ψ : LocalizedModule S M →ₗ[Localization S] LocalizedModule S B =>
        (LocalizedModule.map S β).comp ψ) := by
  obtain ⟨n, f, ⟨e⟩⟩ :=
    finitePresentation_equiv_directSum_quotient_span_singleton
      (Localization S) (LocalizedModule S M)
  intro ψ
  obtain ⟨Φ, hΦ⟩ := exists_lift_of_equiv_directSum_quotient f e
    (LocalizedModule.map S β).ker.subtype (LocalizedModule.map S β)
    (LocalizedModule.map_surjective S β hβ) (Submodule.range_subtype _)
    (by simpa only [Submodule.range_subtype] using localized_ker_pure S β hpure) ψ
  exact ⟨Φ, hΦ⟩

private lemma localized_map_comp {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} {N : Type w} {P : Type x}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    LocalizedModule.map S (g.comp f) =
      (LocalizedModule.map S g).comp (LocalizedModule.map S f) := by
  refine LinearMap.ext fun z => ?_
  induction z using LocalizedModule.induction_on with
  | h m s => simp only [LinearMap.comp_apply, LocalizedModule.map_mk]

private lemma localized_compRight {R : Type u} [CommRing R]
    (S : Submonoid R) {M : Type v} {B : Type w} {C : Type x}
    [AddCommGroup M] [AddCommGroup B] [AddCommGroup C]
    [Module R M] [Module R B] [Module R C]
    [Module.FinitePresentation R M] (β : B →ₗ[R] C)
    (z : LocalizedModule S (M →ₗ[R] B)) :
    (Module.FinitePresentation.linearEquivMapExtendScalars S)
        ((LocalizedModule.map S (LinearMap.compRight R β)) z) =
      (LocalizedModule.map S β).comp
        ((Module.FinitePresentation.linearEquivMapExtendScalars S) z) := by
  let eB : LocalizedModule S (M →ₗ[R] B) ≃ₗ[R]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S B) :=
    Module.FinitePresentation.linearEquivMapExtendScalars S
  let eC : LocalizedModule S (M →ₗ[R] C) ≃ₗ[R]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S C) :=
    Module.FinitePresentation.linearEquivMapExtendScalars S
  let F : (M →ₗ[R] B) →ₗ[R] (M →ₗ[R] C) := LinearMap.compRight R β
  let g₁ : LocalizedModule S (M →ₗ[R] B) →ₗ[R]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S C) :=
    eC.toLinearMap.comp ((LocalizedModule.map S F).restrictScalars R)
  let g₂ : LocalizedModule S (M →ₗ[R] B) →ₗ[R]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S C) :=
    ((LinearMap.compRight (Localization S) (LocalizedModule.map S β)).restrictScalars R).comp
      eB.toLinearMap
  have hg : g₁ = g₂ := by
    apply IsLocalizedModule.linearMap_ext S
      (LocalizedModule.mkLinearMap S (M →ₗ[R] B))
      (LocalizedModule.map S (M := M) (N := C))
    apply LinearMap.ext
    intro φ
    have hcomp := localized_map_comp S φ β
    simp only [g₁, g₂, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, F,
      LinearMap.compRight_apply]
    show (Module.FinitePresentation.linearEquivMapExtendScalars S)
        ((LocalizedModule.mkLinearMap S (M →ₗ[R] C)) (β.comp φ)) =
      (LocalizedModule.map S β).comp
        ((Module.FinitePresentation.linearEquivMapExtendScalars S)
          ((LocalizedModule.mkLinearMap S (M →ₗ[R] B)) φ))
    rw [Module.FinitePresentation.linearEquivMapExtendScalars_apply,
      Module.FinitePresentation.linearEquivMapExtendScalars_apply]
    exact hcomp
  exact LinearMap.congr_fun hg z

private lemma compRight_surjective_of_locally_bezout
    {R : Type u} [CommRing R]
    (hR : ∀ (m : Ideal R) [m.IsMaximal], IsBezout (Localization.AtPrime m))
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {B : Type w} {C : Type x} [AddCommGroup B] [AddCommGroup C]
    [Module R B] [Module R C] (β : B →ₗ[R] C)
    (hβ : Function.Surjective β)
    (hpure : ∀ f : R,
      f • β.ker = β.ker ⊓ f • (⊤ : Submodule R B)) :
    Function.Surjective
      ((LinearMap.compRight R β) : (M →ₗ[R] B) →ₗ[R] (M →ₗ[R] C)) := by
  apply surjective_of_localized_maximal
  intro m hm
  let S := m.primeCompl
  let : IsBezout (Localization S) := hR m
  let eB : LocalizedModule S (M →ₗ[R] B) ≃ₗ[R]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S B) :=
    Module.FinitePresentation.linearEquivMapExtendScalars S
  let eC : LocalizedModule S (M →ₗ[R] C) ≃ₗ[R]
      (LocalizedModule S M →ₗ[Localization S] LocalizedModule S C) :=
    Module.FinitePresentation.linearEquivMapExtendScalars S
  intro z
  obtain ⟨ψ, hψ⟩ := localized_lift S β hβ hpure (eC z)
  refine ⟨eB.symm ψ, ?_⟩
  apply eC.injective
  rwa [localized_compRight, LinearEquiv.apply_symm_apply]

private lemma directSum_subtypeDomain_leftInverse
    {R : Type u} [CommRing R] {I : Type y} [DecidableEq I] (D : I → Type x)
    [∀ j, AddCommGroup (D j)] [∀ j, Module R (D j)]
    [∀ j, DecidableEq (D j)]
    (s : Finset I) (z : ⨁ j, D j) (hz : ↑(DFinsupp.support z) ⊆ (s : Set I)) :
    (DirectSum.toModule R {j // j ∈ s} (⨁ j, D j)
      (fun j => DirectSum.lof R I D j.1))
      ((DFinsupp.subtypeDomainLinearMap R D (fun j => j ∈ s)) z) = z := by
  classical
  let e : (⨁ j, D j) →ₗ[R] ⨁ j : {j // j ∈ s}, D j.1 :=
    DFinsupp.subtypeDomainLinearMap R D (fun j => j ∈ s)
  let q : (⨁ j : {j // j ∈ s}, D j.1) →ₗ[R] ⨁ j, D j :=
    DirectSum.toModule R {j // j ∈ s} (⨁ j, D j)
      (fun j => DirectSum.lof R I D j.1)
  show q (e z) = z
  conv_rhs => rw [← DirectSum.sum_support_of z]
  nth_rewrite 1 [← DirectSum.sum_support_of z]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjs : j ∈ s := hz hj
  have he : e ((DirectSum.lof R I D j) (z j)) =
      (DirectSum.lof R {j // j ∈ s} (fun j => D j.1) ⟨j, hjs⟩) (z j) := by
    apply DirectSum.ext
    intro k
    show ((DirectSum.of D j) (z j)) k.1 =
      ((DirectSum.of (fun j : {j // j ∈ s} => D j.1) ⟨j, hjs⟩) (z j)) k
    by_cases h : j = k.1
    · subst h
      simp
    · have hk : (⟨j, hjs⟩ : {j // j ∈ s}) ≠ k := fun heq => h (congrArg Subtype.val heq)
      simp [DirectSum.of_apply, h, hk]
  rw [← DirectSum.lof_eq_of R I D j, he, DirectSum.toModule_lof]

/-- A finite module that is a direct summand of an arbitrary direct sum of cyclic modules is
already a direct summand of the partial sum over a finite subset of the index set. -/
private lemma finite_summand_of_summand_directSum
    {R : Type u} [CommRing R] {I : Type y} (f : I → R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (i : M →ₗ[R] ⨁ j, R ⧸ Ideal.span {f j})
    (p : (⨁ j, R ⧸ Ideal.span {f j}) →ₗ[R] M)
    (hpi : p.comp i = LinearMap.id) :
    ∃ (s : Finset I)
      (i' : M →ₗ[R] ⨁ j : {j // j ∈ s}, R ⧸ Ideal.span {f j.1})
      (p' : (⨁ j : {j // j ∈ s}, R ⧸ Ideal.span {f j.1}) →ₗ[R] M),
      p'.comp i' = LinearMap.id := by
  classical
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top (R := R) (M := M))
  let s : Finset I := g.biUnion (fun m => DFinsupp.support (i m))
  let D : I → Type u := fun j => R ⧸ Ideal.span {f j}
  let e : (⨁ j, D j) →ₗ[R] ⨁ j : {j // j ∈ s}, D j.1 :=
    DFinsupp.subtypeDomainLinearMap R D (fun j => j ∈ s)
  let q : (⨁ j : {j // j ∈ s}, D j.1) →ₗ[R] ⨁ j, D j :=
    DirectSum.toModule R {j // j ∈ s} (⨁ j, D j)
      (fun j => DirectSum.lof R I D j.1)
  have hsupp (m : M) : ↑(DFinsupp.support (i m)) ⊆ (s : Set I) := by
    rw [DFinsupp.support_subset_iff]
    intro j hj
    have hz : (DirectSum.component R I D j).comp i = 0 := by
      apply LinearMap.ext_on hg
      intro a ha
      have hjg : j ∉ DFinsupp.support (i a) := by
        intro hja
        exact hj (Finset.mem_biUnion.mpr ⟨a, ha, hja⟩)
      by_contra h
      exact hjg (DFinsupp.mem_support_iff.mpr h)
    exact LinearMap.congr_fun hz m
  refine ⟨s, e.comp i, p.comp q, LinearMap.ext fun m => ?_⟩
  show p (q (e (i m))) = m
  rw [directSum_subtypeDomain_leftInverse D s (i m) (hsupp m)]
  exact LinearMap.congr_fun hpi m

/-- Every finitely presented module over a commutative ring whose localizations at maximal ideals
are Bézout rings is a direct summand of a finite direct sum of quotients by principal ideals. -/
@[stacks 0ASQ]
theorem finitePresentation_summand_fin_directSum_quotient_span_singleton
    (R : Type u) [CommRing R]
    (hR : ∀ (m : Ideal R) [m.IsMaximal], IsBezout (Localization.AtPrime m))
    (M : Type v) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ (n : ℕ) (f : Fin n → R)
      (i : M →ₗ[R] ⨁ j, R ⧸ Ideal.span {f j})
      (p : (⨁ j, R ⧸ Ideal.span {f j}) →ₗ[R] M),
      p.comp i = LinearMap.id := by
  classical
  obtain ⟨I, f, ι, π, hπι⟩ :=
    (summand_sum_cyclic_iff_lifting R M).mpr (by
      intro A B C _ _ _ _ _ _ α β _ hβ hex hpure ψ
      have hker : ∀ g : R,
          g • β.ker = β.ker ⊓ g • (⊤ : Submodule R B) := by
        simpa only [hex] using hpure
      obtain ⟨φ, hφ⟩ := compRight_surjective_of_locally_bezout hR β hβ hker ψ
      exact ⟨φ, by simpa only [LinearMap.compRight_apply] using hφ⟩)
  obtain ⟨s, i', p', hpi'⟩ := finite_summand_of_summand_directSum f ι π hπι
  let e : (↑s : Type (max u v)) ≃ Fin (Fintype.card (↑s : Type (max u v))) := Fintype.equivFin _
  let g : Fin (Fintype.card (↑s : Type (max u v))) → R := fun j => f (e.symm j).1
  let E : (⨁ j : (↑s : Type (max u v)), R ⧸ Ideal.span {f j.1}) ≃ₗ[R]
      ⨁ j : Fin (Fintype.card (↑s : Type (max u v))), R ⧸ Ideal.span {g j} :=
    DirectSum.lequivCongrLeft R e
  refine ⟨Fintype.card (↑s : Type (max u v)), g,
    E.toLinearMap.comp i', p'.comp E.symm.toLinearMap, LinearMap.ext fun m => ?_⟩
  show p' (E.symm (E (i' m))) = m
  rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun hpi' m
