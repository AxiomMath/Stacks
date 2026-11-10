module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.MvPowerSeries.Noetherian
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Minimal presentations of a local `ℤ_[ℓ]`-algebra by power series

Let `R` be a local `ℤ_[ℓ]`-algebra, finite as a `ℤ_[ℓ]`-module, whose residue field is the image of
`ℤ_[ℓ]`, and let `y₁, …, y_d ∈ 𝔪_R` generate `𝔪_R` modulo `𝔪_R² + ℓR` with `d` minimal. Then the
map `F : ℤ_[ℓ][[x₁, …, x_d]] → R` sending `xᵢ` to `yᵢ` is surjective, and by the minimality of `d`
its kernel lies in `𝔪² + ℓ P`.

The second half concerns minimal generating families `f₁, …, f_r` of an ideal `J` of a local
ring: by Nakayama no relation `∑ pᵢ fᵢ = 0` has a unit coefficient.

## Main definitions

* `IsLocalRing.IsCotangentFamily`: a family of elements of `𝔪_R` generating `𝔪_R` modulo
  `𝔪_R² + ℓR`.

## Main results

* `IsLocalRing.coeff_mem_of_minimal`: in a relation modulo `𝔪_R² + ℓR` among a cotangent family
  of minimal length, every coefficient lies in `ℓ ℤ_[ℓ]`.
* `IsLocalRing.surjective_of_cotangentFamily`: the power series map is surjective.
* `IsLocalRing.ker_le_of_minimal`: its kernel lies in `𝔪_P² + ℓP`.
* `IsLocalRing.exists_minimal_generators`: a finitely generated ideal of a local ring has a
  generating family admitting no relation with a unit coefficient.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsLocalRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {R : Type*} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]

/-- A family of elements of `𝔪_R` generating `𝔪_R` modulo `𝔪_R² + ℓR`. -/
def IsCotangentFamily {d : ℕ} (y : Fin d → R) : Prop :=
  (∀ i, y i ∈ maximalIdeal R) ∧
    maximalIdeal R ≤ Ideal.span (Set.range y) ⊔ maximalIdeal R ^ 2 ⊔
      Ideal.span {algebraMap ℤ_[ℓ] R ℓ}

/-- A Noetherian local `ℤ_[ℓ]`-algebra admits a finite cotangent family. -/
lemma exists_isCotangentFamily [IsNoetherianRing R] :
    ∃ d : ℕ, ∃ y : Fin d → R, IsCotangentFamily (ℓ := ℓ) y := by
  obtain ⟨d, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    ((isNoetherianRing_iff_ideal_fg R).1 inferInstance (maximalIdeal R))
  refine ⟨d, y, fun i => hy ▸ Ideal.subset_span ⟨i, rfl⟩, ?_⟩
  exact (le_of_eq hy.symm).trans (le_sup_left.trans le_sup_left)

/-- **The minimality property of a minimal cotangent family**: in a relation
`∑ cᵢ yᵢ ∈ 𝔪² + ℓR` with `cᵢ ∈ ℤ_[ℓ]` every coefficient is divisible by `ℓ`. -/
theorem coeff_mem_of_minimal {d : ℕ} (y : Fin d → R) (hy : IsCotangentFamily (ℓ := ℓ) y)
    (hmin : ∀ (d' : ℕ) (y' : Fin d' → R), IsCotangentFamily (ℓ := ℓ) y' → d ≤ d')
    (c : Fin d → ℤ_[ℓ])
    (hc : ∑ i, algebraMap ℤ_[ℓ] R (c i) * y i ∈
      maximalIdeal R ^ 2 ⊔ Ideal.span {algebraMap ℤ_[ℓ] R ℓ}) (k : Fin d) :
    c k ∈ maximalIdeal ℤ_[ℓ] := by
  by_contra hk
  have hu : IsUnit (c k) := by
    by_contra hu; exact hk ((mem_maximalIdeal _).mpr hu)
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by have := k.2; omega⟩
  set y' : Fin d' → R := y ∘ k.succAbove
  set K : Ideal R := Ideal.span (Set.range y') ⊔ maximalIdeal R ^ 2 ⊔
    Ideal.span {algebraMap ℤ_[ℓ] R ℓ}
  have hyk : y k ∈ K := by
    have hsplit := Fin.sum_univ_succAbove (fun i => algebraMap ℤ_[ℓ] R (c i) * y i) k
    have h1 : algebraMap ℤ_[ℓ] R (c k) * y k ∈ K := by
      have h2 : ∑ i : Fin d', algebraMap ℤ_[ℓ] R (c (k.succAbove i)) * y (k.succAbove i) ∈ K :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
          (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)))
      have h3 : ∑ i, algebraMap ℤ_[ℓ] R (c i) * y i ∈ K := by
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hc
        rw [← hab]
        exact K.add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right ha)) (Ideal.mem_sup_right hb)
      rw [hsplit] at h3
      have := K.sub_mem h3 h2
      simpa using this
    exact (Ideal.unit_mul_mem_iff_mem K (hu.map _)).1 h1
  have hy' : IsCotangentFamily (ℓ := ℓ) y' := by
    refine ⟨fun i => hy.1 _, hy.2.trans ?_⟩
    refine sup_le (sup_le ?_ (le_sup_right.trans le_sup_left)) le_sup_right
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = k
    · rw [hi]; exact hyk
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩))
  have := hmin d' y' hy'
  omega

/-- **The power series map attached to a cotangent family is surjective**, for an `R` which is
finite over `ℤ_[ℓ]`, Noetherian, with residue field the image of `ℤ_[ℓ]` and finite special
fibre. -/
theorem surjective_of_cotangentFamily [IsNoetherianRing R] [Module.Finite ℤ_[ℓ] R]
    (hres : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal R)).comp
      (algebraMap ℤ_[ℓ] R)))
    (hfin : Finite (R ⧸ Ideal.span {algebraMap ℤ_[ℓ] R ℓ}))
    {d : ℕ} (y : Fin d → R) (hy : IsCotangentFamily (ℓ := ℓ) y)
    (F : MvPowerSeries (Fin d) ℤ_[ℓ] →+* R) (hFX : ∀ i, F (MvPowerSeries.X i) = y i)
    (hFC : ∀ c, F (MvPowerSeries.C c) = algebraMap ℤ_[ℓ] R c) : Function.Surjective F := by
  classical
  set L : Ideal R := Ideal.span {algebraMap ℤ_[ℓ] R ℓ}
  set m := maximalIdeal R
  have hmmax : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have hLm : L ≤ m := by
    rw [Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    let : Field (R ⧸ m) := Ideal.Quotient.field m
    have hmax : (RingHom.ker ((Ideal.Quotient.mk (maximalIdeal R)).comp
        (algebraMap ℤ_[ℓ] R))).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hres
    have hle := IsLocalRing.eq_maximalIdeal hmax
    have hℓ : (ℓ : ℤ_[ℓ]) ∈ maximalIdeal ℤ_[ℓ] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.subset_span rfl
    rw [← hle, RingHom.mem_ker] at hℓ
    exact hℓ
  have hmeq : m ≤ Ideal.span (Set.range y) ⊔ L := by
    have hfg : (m : Submodule R R).FG := (isNoetherianRing_iff_ideal_fg R).1 inferInstance m
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
    refine hy.2.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) ?_)
      (le_sup_right.trans le_sup_left))
    rw [pow_two, Ideal.smul_eq_mul]
    exact le_sup_right
  set S : Subring R := F.range
  have hyS : ∀ i, y i ∈ S := fun i => ⟨_, hFX i⟩
  have hcS : ∀ c, algebraMap ℤ_[ℓ] R c ∈ S := fun c => ⟨_, hFC c⟩
  have hR1 : ∀ a : R, ∃ s ∈ S, a - s ∈ m := by
    intro a
    obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk m a)
    exact ⟨_, hcS c, by
      rw [← Ideal.Quotient.eq, ← hc]; rfl⟩
  set G : Set R := insert (algebraMap ℤ_[ℓ] R ℓ) (Set.range y)
  have hGS : G ⊆ S := by
    rintro _ (rfl | ⟨i, rfl⟩); exacts [hcS _, hyS i]
  have hGm : G ⊆ m := by
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hLm (Ideal.subset_span rfl)
    · exact hy.1 i
  have hmG : m = Ideal.span G := by
    refine le_antisymm (hmeq.trans (sup_le (Ideal.span_mono (Set.subset_insert _ _))
      (Ideal.span_mono (by simp [G])))) (Ideal.span_le.mpr hGm)
  have hstep : ∀ k, ∀ x ∈ m ^ k, ∃ s ∈ S, s ∈ m ^ k ∧ x - s ∈ m ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro x _
      obtain ⟨s, hs, hxs⟩ := hR1 x
      exact ⟨s, hs, by simp, by simpa using hxs⟩
    | succ k ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        obtain ⟨sa, hsa, hsam, hea⟩ := ih a ha
        have hb' : ∃ sb ∈ S, sb ∈ m ∧ b - sb ∈ m ^ 2 := by
          rw [hmG] at hb
          refine Submodule.span_induction (p := fun b _ => ∃ sb ∈ S, sb ∈ m ∧ b - sb ∈ m ^ 2)
            ?_ ⟨0, S.zero_mem, m.zero_mem, by simp⟩ ?_ ?_ hb
          · intro g hg
            exact ⟨g, hGS hg, hGm hg, by simp⟩
          · rintro u v - - ⟨su, hsu, hsum, heu⟩ ⟨sv, hsv, hsvm, hev⟩
            exact ⟨su + sv, S.add_mem hsu hsv, m.add_mem hsum hsvm, by
              rw [add_sub_add_comm]; exact Ideal.add_mem _ heu hev⟩
          · rintro r u - ⟨su, hsu, hsum, heu⟩
            obtain ⟨sr, hsr, her⟩ := hR1 r
            refine ⟨sr * su, S.mul_mem hsr hsu, m.mul_mem_left _ hsum, ?_⟩
            have : r • u - sr * su = r * (u - su) + (r - sr) * su := by
              rw [smul_eq_mul]; ring
            rw [this]
            refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ heu) ?_
            rw [pow_two]; exact Ideal.mul_mem_mul her hsum
        obtain ⟨sb, hsb, hsbm, heb⟩ := hb'
        refine ⟨sa * sb, S.mul_mem hsa hsb, ?_, ?_⟩
        · rw [pow_succ]; exact Ideal.mul_mem_mul hsam hsbm
        · have : a * b - sa * sb = sa * (b - sb) + (a - sa) * b := by ring
          rw [this]
          refine Ideal.add_mem _ ?_ ?_
          · have : m ^ k * m ^ 2 = m ^ (k + 1 + 1) := by rw [← pow_add]
            rw [← this]; exact Ideal.mul_mem_mul hsam heb
          · rw [pow_succ _ (k + 1)]; exact Ideal.mul_mem_mul hea hb
      · rintro u v ⟨su, hsu, hsum, heu⟩ ⟨sv, hsv, hsvm, hev⟩
        exact ⟨su + sv, S.add_mem hsu hsv, Ideal.add_mem _ hsum hsvm, by
          rw [add_sub_add_comm]; exact Ideal.add_mem _ heu hev⟩
  have hdense : ∀ k, ∀ a : R, ∃ s ∈ S, a - s ∈ m ^ k := by
    intro k
    induction k with
    | zero => intro a; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro a
      obtain ⟨s, hs, has⟩ := ih a
      obtain ⟨s', hs', -, hs''⟩ := hstep k _ has
      exact ⟨s + s', S.add_mem hs hs', by rwa [sub_add_eq_sub_sub]⟩
  have : IsArtinianRing (R ⧸ L) := isArtinian_of_finite
  have : Nontrivial (R ⧸ L) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top hLm)
  have : IsLocalRing (R ⧸ L) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ L)
  have hmN : m ^ N ≤ L := by
    intro x hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hmap : (m ^ N).map (Ideal.Quotient.mk L) ≤ (Ideal.jacobson (⊥ : Ideal (R ⧸ L))) ^ N := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ N
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top,
        ← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    have := hmap (Ideal.mem_map_of_mem _ hx)
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  let S' : Submodule ℤ_[ℓ] R :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := fun c x hx => by rw [Algebra.smul_def]; exact S.mul_mem (hcS c) hx }
  have htop : (⊤ : Submodule ℤ_[ℓ] R) ≤ S' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
    intro a _
    obtain ⟨s, hs, has⟩ := hdense N a
    have h1 : a - s ∈ (maximalIdeal ℤ_[ℓ]) • (⊤ : Submodule ℤ_[ℓ] R) := by
      have h2 := hmN has
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h2
      rw [← hr, PadicInt.maximalIdeal_eq_span_p, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem_smul (Ideal.subset_span rfl) trivial
    rw [show a = s + (a - s) by ring]
    exact Submodule.add_mem_sup hs h1
  intro a
  obtain ⟨p, hp⟩ := htop (Submodule.mem_top (x := a))
  exact ⟨p, hp⟩

open Stacks.CompleteLocalRing.RegularSubring in
/-- **The kernel of a minimal presentation lies in `𝔪_P² + ℓP`.** -/
theorem ker_le_of_minimal {d : ℕ} (y : Fin d → R) (hy : IsCotangentFamily (ℓ := ℓ) y)
    (hmin : ∀ (d' : ℕ) (y' : Fin d' → R), IsCotangentFamily (ℓ := ℓ) y' → d ≤ d')
    (F : MvPowerSeries (Fin d) ℤ_[ℓ] →+* R) (hF : Function.Surjective F)
    (hFX : ∀ i, F (MvPowerSeries.X i) = y i)
    (hFC : ∀ c, F (MvPowerSeries.C c) = algebraMap ℤ_[ℓ] R c) :
    RingHom.ker F ≤ maximalIdeal (MvPowerSeries (Fin d) ℤ_[ℓ]) ^ 2 ⊔
      Ideal.span {MvPowerSeries.C (ℓ : ℤ_[ℓ])} := by
  classical
  set P := MvPowerSeries (Fin d) ℤ_[ℓ]
  set mP := maximalIdeal P
  have hcomap : (maximalIdeal R).comap F = mP :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective F hF)
  have hmP : mP = Ideal.span {MvPowerSeries.C (ℓ : ℤ_[ℓ])} ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin d → P)) := by
    change maximalIdeal (MvPowerSeries (Fin d) ℤ_[ℓ]) = _
    rw [maximalIdeal_mvPowerSeries, PadicInt.maximalIdeal_eq_span_p, Ideal.map_span,
      Set.image_singleton]
  have hFm : ∀ q ∈ mP, F q ∈ maximalIdeal R := fun q hq => by
    rw [← hcomap] at hq; exact hq
  intro j hj
  have hjm : j ∈ mP := by
    rw [← hcomap, Ideal.mem_comap, (RingHom.mem_ker).mp hj]; exact Submodule.zero_mem _
  rw [hmP] at hjm
  obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := Submodule.mem_sup.mp hjm
  obtain ⟨p, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun P).mp hj₂
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hj₁
  set a : Fin d → ℤ_[ℓ] := fun i => MvPowerSeries.constantCoeff (p i)
  have hq : ∀ i, p i - MvPowerSeries.C (a i) ∈ mP := fun i => by
    rw [hmP]
    exact Ideal.mem_sup_right (mem_span_range_X d _ (by simp [a]))
  have hrel : ∑ i, algebraMap ℤ_[ℓ] R (a i) * y i ∈
      maximalIdeal R ^ 2 ⊔ Ideal.span {algebraMap ℤ_[ℓ] R ℓ} := by
    have h0 := (RingHom.mem_ker).mp hj
    simp only [map_add, map_mul, map_sum, smul_eq_mul, hFX, hFC] at h0
    have : ∑ i, algebraMap ℤ_[ℓ] R (a i) * y i =
        -(F t * algebraMap ℤ_[ℓ] R ℓ) - ∑ i, (F (p i) - algebraMap ℤ_[ℓ] R (a i)) * y i := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      linear_combination h0
    rw [this]
    refine Ideal.sub_mem _ (neg_mem (Ideal.mem_sup_right
      (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))) (Ideal.mem_sup_left ?_)
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (hy.1 i)
    have := hFm _ (hq i)
    rwa [map_sub, hFC] at this
  have ha : ∀ i, a i ∈ maximalIdeal ℤ_[ℓ] := coeff_mem_of_minimal y hy hmin a hrel
  refine Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
    (Ideal.sum_mem _ fun i _ => ?_)
  rw [smul_eq_mul, show p i = (p i - MvPowerSeries.C (a i)) + MvPowerSeries.C (a i) by ring,
    add_mul]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
  · rw [pow_two]
    refine Ideal.mul_mem_mul (hq i) ?_
    rw [hmP]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  · have := ha i
    rw [PadicInt.maximalIdeal_eq_span_p] at this
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp this
    exact Ideal.mem_span_singleton'.mpr ⟨MvPowerSeries.C b * MvPowerSeries.X i, by
      rw [← hb, map_mul]; ring⟩

/-- Dropping a generator with a unit coefficient in a relation. -/
theorem span_succAbove_eq_of_isUnit {P : Type*} [CommRing P] {r : ℕ} (f : Fin (r + 1) → P)
    (p : Fin (r + 1) → P) (hp : ∑ i, p i * f i = 0) (k : Fin (r + 1)) (hu : IsUnit (p k)) :
    Ideal.span (Set.range (f ∘ k.succAbove)) = Ideal.span (Set.range f) := by
  have hsub : f k ∈ Ideal.span (Set.range (f ∘ k.succAbove)) := by
    have hsplit := Fin.sum_univ_succAbove (fun i => p i * f i) k
    rw [hp] at hsplit
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [eq_neg_of_add_eq_zero_left hsplit.symm]
    exact neg_mem (Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  refine le_antisymm (Ideal.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩)) ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hik : i = k
  · rw [hik]; exact hsub
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hik
    exact Ideal.subset_span ⟨j, rfl⟩

/-- **Minimal generating families of an ideal of a local ring.** A generating family of minimal
length of a finitely generated ideal admits no relation with a unit coefficient. -/
theorem exists_minimal_generators {P : Type*} [CommRing P] [IsLocalRing P] (J : Ideal P)
    (hJ : J.FG) :
    ∃ r : ℕ, ∃ f : Fin r → P, Ideal.span (Set.range f) = J ∧
      ∀ p : Fin r → P, ∑ i, p i * f i = 0 → ∀ i, p i ∈ maximalIdeal P := by
  classical
  have hex : ∃ r : ℕ, ∃ f : Fin r → P, Ideal.span (Set.range f) = J :=
    Submodule.fg_iff_exists_fin_generating_family.1 hJ
  obtain ⟨r, ⟨f, hf⟩, hmin⟩ : ∃ r : ℕ, (∃ f : Fin r → P, Ideal.span (Set.range f) = J) ∧
      ∀ r' : ℕ, (∃ f : Fin r' → P, Ideal.span (Set.range f) = J) → r ≤ r' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r' h => Nat.find_min' hex h⟩
  refine ⟨r, f, hf, fun p hp k => ?_⟩
  by_contra hk
  have hu : IsUnit (p k) := by
    by_contra hu; exact hk ((mem_maximalIdeal _).mpr hu)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := k.2; omega⟩
  have := hmin r' ⟨f ∘ k.succAbove, (span_succAbove_eq_of_isUnit f p hp k hu).trans hf⟩
  omega

end IsLocalRing
