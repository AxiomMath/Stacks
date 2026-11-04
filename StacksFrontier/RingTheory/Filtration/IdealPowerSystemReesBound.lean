module

public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian

/-!
# Parts (1) and (2) of [Stacks, Tag 02OA] for a Rees system

`Stacks.RingTheory.ReesSystem.isNoetherianSystem_of_isReesFinite` turns the finiteness of
`⨁ₙ Mₙ` over the Rees algebra `⨁ₙ Iⁿ` into the Noetherianity that the Artin–Rees argument of
`Stacks.RingTheory.IdealPowerSystem.exists_uniform_bound` consumes, which gives parts (2) at
`n = 0` and (3) of [Stacks, Tag 02OA]. Parts (1) and (2) at a general `n` need two further
laws relating the transition maps to the multiplication maps, recorded here as the predicate
`Stacks.RingTheory.ReesSystem.IsTrMulCompatible`:

* the multiplication maps commute with the transition maps (`tr_mul`), and
* multiplying by `a ∈ Iᵏ` and dropping back to the degree one started in is the action of `a`
  (`tr_mul_self`).

Both hold for `n ↦ Hᵖ(X, Iⁿ F)`, because every map in sight is multiplication by one function on
the base; that is
`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem_isTrMulCompatible`.

## Main results

* `Stacks.RingTheory.ReesSystem.mulSpan_eq_top`: part (1) of [Stacks, Tag 02OA] --
  `Iⁿ⁻ᶜ · M_c = Mₙ` for `n ≥ c`.
* `Stacks.RingTheory.ReesSystem.range_tr_le`: part (2) of [Stacks, Tag 02OA] at every `n`.
* `Stacks.RingTheory.ReesSystem.exists_uniform_bound_rees`: one constant serving parts (1),
  (2) and (3).

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
-/

@[expose] public section

open DirectSum Stacks.Blowup

universe u u' v w

namespace Stacks.RingTheory

variable {A : Type u'} [CommRing A] {R : Type u} [CommRing R] {φ : A →+* R} {I : Ideal A}
  {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]

namespace ReesSystem

variable (S : ReesSystem φ I M M₀)

/-- **The two laws relating the transition maps of a Rees system to its multiplication maps.**
Multiplying by `a ∈ Iᵏ` and then dropping from degree `k + n` to degree `k + m` is dropping from
`n` to `m` and then multiplying by `a` (`tr_mul`); and multiplying by `a ∈ Iᵏ` and dropping back
to the degree one started in is the module action of `a` (`tr_mul_self`, the statement
`proj_mul` makes about `M₀`, made about every `Mₙ`). These are what parts (1) and (2) of
[Stacks, Tag 02OA] run on. -/
structure IsTrMulCompatible : Prop where
  tr_mul : ∀ (k n m : ℕ) (h : m ≤ n) (a : ↥(I ^ k)) (x : M n),
    S.tr (Nat.add_le_add_left h k) (S.mul k n ⟨φ a, map_mem_map_pow φ I a.2⟩ x) =
      S.mul k m ⟨φ a, map_mem_map_pow φ I a.2⟩ (S.tr h x)
  tr_mul_self : ∀ (k n : ℕ) (a : ↥(I ^ k)) (x : M n),
    S.tr (Nat.le_add_left n k) (S.mul k n ⟨φ a, map_mem_map_pow φ I a.2⟩ x) = φ a • x

/-- **The identity law.** A transition map between equal degrees is the identity. This is the
field `tr_of_eq` with its index equality discharged. -/
theorem tr_self {n : ℕ} (h : n ≤ n) (x : M n) : S.tr h x = x := by
  have hs := S.tr_of_eq h rfl x
  rw [Sigma.mk.injEq] at hs
  exact eq_of_heq hs.2

/-- A transition map applied to the two sides of an equality in `Σ n, Mₙ`. The index equality
the sigma equality carries is what makes this a statement about a single transition map. -/
theorem tr_congr_sigma {i i' m : ℕ} {y : M i} {y' : M i'}
    (hy : (⟨i, y⟩ : Σ j, M j) = ⟨i', y'⟩) (h : m ≤ i) (h' : m ≤ i') :
    S.tr h y = S.tr h' y' := by
  injection hy with h1 h2
  subst h1
  rw [eq_of_heq h2]

/-- The commutation `tr ∘ mul = mul ∘ tr`, followed by a further drop. -/
theorem tr_tr_mul (hS : S.IsTrMulCompatible) {k n m j : ℕ} (hm : m ≤ n) (hj : j ≤ k + m)
    (a : ↥(I ^ k)) (x : M n) :
    S.tr (hj.trans (Nat.add_le_add_left hm k))
        (S.mul k n ⟨φ a, map_mem_map_pow φ I a.2⟩ x) =
      S.tr hj (S.mul k m ⟨φ a, map_mem_map_pow φ I a.2⟩ (S.tr hm x)) := by
  rw [← S.tr_tr hj (Nat.add_le_add_left hm k), hS.tr_mul]

/-- **The multiples of `Mₘ` by `Iᵏ`**, read in a degree `n ≤ k + m`: the `R`-submodule of `Mₙ`
spanned by the transition images of the products `a · y` with `a ∈ Iᵏ` and `y : Mₘ`. Part (1)
of [Stacks, Tag 02OA] is that `mulSpan (n - c) c n` is everything for `n ≥ c`, which is the
surjectivity of the multiplication map `Iⁿ⁻ᶜ ⊗ M_c → Mₙ`. -/
def mulSpan (k m n : ℕ) (h : n ≤ k + m) : Submodule R (M n) :=
  Submodule.span R (Set.range fun q : ↥(I ^ k) × M m ↦
    S.tr h (S.mul k m ⟨φ q.1, map_mem_map_pow φ I q.1.2⟩ q.2))

/-- A single product lies in the span of the products. -/
theorem mem_mulSpan {k m n : ℕ} (h : n ≤ k + m) (a : ↥(I ^ k)) (y : M m) :
    S.tr h (S.mul k m ⟨φ a, map_mem_map_pow φ I a.2⟩ y) ∈ S.mulSpan k m n h :=
  Submodule.subset_span ⟨(a, y), rfl⟩

/-- The span of the products depends on the source degree only through its value. -/
theorem mulSpan_congr {k m m' n : ℕ} (e : m = m') (h : n ≤ k + m) (h' : n ≤ k + m') :
    S.mulSpan k m n h = S.mulSpan k m' n h' := by subst e; rfl

/-- **Splitting the acting degree.** A multiple of `y` by an element of `Iᵏ⁺ˡ` is a sum of
multiples by `Iᵏ` of multiples by `Iˡ`: the associativity `mul_mul` applied to a decomposition
of the coefficient in `Iᵏ · Iˡ = Iᵏ⁺ˡ`. -/
theorem tr_mul_mem_mulSpan {k l j m n : ℕ} (hj : k + l = j) (h : n ≤ j + m)
    (h' : n ≤ k + (l + m)) (y : M m) :
    ∀ (r : A) (_ : r ∈ I ^ k * I ^ l) (hr : r ∈ I ^ j),
      S.tr h (S.mul j m ⟨φ r, map_mem_map_pow φ I hr⟩ y) ∈ S.mulSpan k (l + m) n h' := by
  subst hj
  intro r hr
  induction hr using Submodule.mul_induction_on' with
  | mem_mul_mem u hu v hv =>
      intro hr'
      rw [S.tr_congr_sigma (S.mul_mul k l m ⟨u, hu⟩ ⟨v, hv⟩ ⟨u * v, hr'⟩ y rfl) h h']
      exact S.mem_mulSpan h' ⟨u, hu⟩ _
  | add z hz z' hz' Cz Cz' =>
      intro hr'
      have hz₁ : z ∈ I ^ (k + l) := (pow_add I k l).ge hz
      have hz₂ : z' ∈ I ^ (k + l) := (pow_add I k l).ge hz'
      have hsplit : (⟨φ (z + z'), map_mem_map_pow φ I hr'⟩ : ↥((I.map φ) ^ (k + l))) =
          ⟨φ z, map_mem_map_pow φ I hz₁⟩ + ⟨φ z', map_mem_map_pow φ I hz₂⟩ :=
        Subtype.ext (map_add φ z z')
      rw [hsplit, map_add, LinearMap.add_apply, map_add]
      exact Submodule.add_mem _ (Cz hz₁) (Cz' hz₂)

/-- **[Stacks, Tag 02OA] part (1), for a Rees system.** If homogeneous elements of degrees at
most `c` generate the system, then `Iⁿ⁻ᶜ · M_c = Mₙ` for every `n ≥ c`: every class in degree
`n` is a sum of multiples by `Iⁿ⁻ᶜ` of classes in degree `c`. -/
theorem mulSpan_eq_top {t : ℕ} {d : Fin t → ℕ} {x : ∀ i, M (d i)}
    (hgen : ∀ (n : ℕ) (z : M n), ∃ a : ∀ i : Fin t, ↥(I ^ (n - d i)),
      z = ∑ i, S.tr (show n ≤ n - d i + d i by omega)
        (S.mul (n - d i) (d i) ⟨φ (a i), map_mem_map_pow φ I (a i).2⟩ (x i)))
    {c : ℕ} (hc : ∀ i, d i ≤ c) (n : ℕ) (hn : c ≤ n) :
    S.mulSpan (n - c) c n (show n ≤ n - c + c by omega) = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨a, ha⟩ := hgen n z
  rw [ha]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have hdi : d i ≤ c := hc i
  have hmem : ((a i : A)) ∈ I ^ (n - c) * I ^ (c - d i) := by
    rw [← pow_add, show (n - c) + (c - d i) = n - d i by omega]
    exact (a i).2
  have hle : n ≤ (n - c) + ((c - d i) + d i) := by omega
  have hin := S.tr_mul_mem_mulSpan (k := n - c) (l := c - d i) (j := n - d i) (m := d i)
    (by omega) (show n ≤ n - d i + d i by omega) hle (x i) (a i) hmem (a i).2
  rwa [S.mulSpan_congr (show (c - d i) + d i = c by omega) hle
    (show n ≤ n - c + c by omega)] at hin

/-- **[Stacks, Tag 02OA] part (2), for a Rees system, at every `n`.** The image of
`M_{n+m} → Mₙ` lies in `Iᵐ⁻ᵉ · Mₙ` with `e = max (0, c - n)`. For `c ≤ n` this is `Iᵐ · Mₙ`,
and for `c > n` it is `Iⁿ⁺ᵐ⁻ᶜ · Mₙ`; both cases are part (1) at the bound `max n c` followed by
the commutation `tr ∘ mul = mul ∘ tr` and the law `tr_mul_self`. -/
theorem range_tr_le (hS : S.IsTrMulCompatible) {t : ℕ} {d : Fin t → ℕ} {x : ∀ i, M (d i)}
    (hgen : ∀ (n : ℕ) (z : M n), ∃ a : ∀ i : Fin t, ↥(I ^ (n - d i)),
      z = ∑ i, S.tr (show n ≤ n - d i + d i by omega)
        (S.mul (n - d i) (d i) ⟨φ (a i), map_mem_map_pow φ I (a i).2⟩ (x i)))
    {c : ℕ} (hc : ∀ i, d i ≤ c) (n m : ℕ) (hnm : c ≤ n + m) :
    LinearMap.range (S.tr (Nat.le_add_right n m)) ≤
      (I.map φ) ^ (m - (c - n)) • (⊤ : Submodule R (M n)) := by
  have hc'gen : ∀ i, d i ≤ max n c := fun i ↦ (hc i).trans (le_max_right n c)
  have hc'le : max n c ≤ n + m := max_le (Nat.le_add_right n m) hnm
  have hk : n + m - max n c = m - (c - n) := by omega
  have hle : n + m ≤ n + m - max n c + max n c := by omega
  have key : S.mulSpan (n + m - max n c) (max n c) (n + m) hle ≤
      Submodule.comap (S.tr (Nat.le_add_right n m))
        ((I.map φ) ^ (m - (c - n)) • (⊤ : Submodule R (M n))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, y⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [S.tr_tr (Nat.le_add_right n m) hle,
      S.tr_tr_mul hS (le_max_left n c) (Nat.le_add_left n (n + m - max n c)) u y,
      hS.tr_mul_self, ← hk]
    exact Submodule.smul_mem_smul (map_mem_map_pow φ I u.2) Submodule.mem_top
  rintro w ⟨z, rfl⟩
  exact key (by rw [S.mulSpan_eq_top hgen hc'gen (n + m) hc'le]; exact Submodule.mem_top)

/-- **Homogeneous generators of the whole system, with coefficients in powers of `I`.** This
is `exists_homogeneous_generators` at the whole system, with the coefficients read as elements
of `Iⁿ⁻ᵈ` rather than of the Rees algebra, and with the index equality `n - d i + d i = n`
discharged by the identity law `tr_of_eq`. -/
theorem exists_pow_generators [IsNoetherianRing A] (hfin : S.IsReesFinite) :
    ∃ (t : ℕ) (d : Fin t → ℕ) (x : ∀ i, M (d i)),
      ∀ (n : ℕ) (z : M n), ∃ a : ∀ i : Fin t, ↥(I ^ (n - d i)),
        z = ∑ i, S.tr (show n ≤ n - d i + d i by omega)
          (S.mul (n - d i) (d i) ⟨φ (a i), map_mem_map_pow φ I (a i).2⟩ (x i)) := by
  let inst := S.gmodule
  have hfin' : Module.Finite (⨁ n, ↥(reesGrading I n)) (⨁ n, M n) := hfin
  have hnoeth : IsNoetherianRing (⨁ n, ↥(reesGrading I n)) :=
    isNoetherianRing_reesGradingDirectSum I
  obtain ⟨t, d, x, -, hcoef⟩ :=
    exists_homogeneous_generators (A := fun n ↦ ↥(reesGrading I n))
      (fun n ↦ (⊤ : Submodule R (M n))) (fun _ _ _ _ _ ↦ Submodule.mem_top)
  refine ⟨t, d, x, fun n z ↦ ?_⟩
  obtain ⟨c, hc0, hceq⟩ := hcoef n z Submodule.mem_top
  have hz' : z = ∑ i, S.tr (show n ≤ n - d i + d i by omega)
      (S.mul (n - d i) (d i) (coeff (φ := φ) (c i)) (x i)) := by
    refine DirectSum.of_injective n ?_
    rw [hceq, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : n < d i
    · rw [hc0 i hi]
      simp only [DirectSum.Gmodule.zero_smul, coeff_zero, map_zero, LinearMap.zero_apply]
    · exact (DirectSum.of_eq_of_gradedMonoid_eq
        (S.tr_of_eq (show n ≤ n - d i + d i by omega) (by omega) _)).symm
  exact ⟨fun i ↦ (reesGradingEquivPow I (n - d i)).symm (c i), hz'⟩

/-- **Parts (1), (2) and (3) of [Stacks, Tag 02OA] with one constant, for a Rees system.**
From the single finiteness input `IsReesFinite` one constant `c` serves: the surjectivity of
`Iⁿ⁻ᶜ ⊗ M_c → Mₙ` for `n ≥ c`; the containment of the image of `M_{n+m} → Mₙ` in
`Iᵐ⁻ᵉ · Mₙ` with `e = max (0, c - n)`; the containment of the image of `M_r → M₀` in
`Iʳ⁻ᶜ · M₀`; and the equality of the kernels out of `M_k`. -/
theorem exists_uniform_bound_rees [IsNoetherianRing A] (hS : S.IsTrMulCompatible)
    (hfin : S.IsReesFinite) :
    ∃ c : ℕ,
      (∀ n : ℕ, c ≤ n → S.mulSpan (n - c) c n (show n ≤ n - c + c by omega) = ⊤) ∧
      (∀ n m : ℕ, c ≤ n + m → LinearMap.range (S.tr (Nat.le_add_right n m)) ≤
        (I.map φ) ^ (m - (c - n)) • (⊤ : Submodule R (M n))) ∧
      (∀ r : ℕ, c ≤ r → LinearMap.range (S.proj r) ≤
        (I.map φ) ^ (r - c) • (⊤ : Submodule R M₀)) ∧
      (∀ (m k : ℕ) (hmk : m + c ≤ k), LinearMap.ker (S.proj k) =
        LinearMap.ker (S.tr (show m ≤ k from le_trans (Nat.le_add_right m c) hmk))) := by
  obtain ⟨t, d, x, hgen⟩ := S.exists_pow_generators hfin
  obtain ⟨c₂, h2, h3⟩ := S.toIdealPowerSystem.exists_uniform_bound
    (S.isNoetherianSystem_of_isReesFinite hfin)
  have hc : ∀ i, d i ≤ max (Finset.univ.sup d) c₂ :=
    fun i ↦ (Finset.le_sup (Finset.mem_univ i)).trans (le_max_left _ _)
  refine ⟨max (Finset.univ.sup d) c₂, fun n hn ↦ S.mulSpan_eq_top hgen hc n hn,
    fun n m hnm ↦ S.range_tr_le hS hgen hc n m hnm, fun r hr ↦ ?_, fun m k hmk ↦ ?_⟩
  · refine (h2 r (le_trans (le_max_right _ _) hr)).trans
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right ?_))
    have := le_max_right (Finset.univ.sup d) c₂
    omega
  · exact h3 m k (le_trans (Nat.add_le_add_left (le_max_right _ _) m) hmk)

end ReesSystem

end Stacks.RingTheory

end
