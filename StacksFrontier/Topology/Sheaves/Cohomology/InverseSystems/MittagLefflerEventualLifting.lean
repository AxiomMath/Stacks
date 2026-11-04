module

public import Mathlib.Algebra.Category.ModuleCat.Images
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.Ideal.Operations
public import StacksFrontier.CategoryTheory.Abelian.InverseSystem

/-!
# Mittag-Leffler from obstructions that eventually lift

Let `A` be a commutative ring, `I ⊆ A` an ideal and `… → H₂ → H₁ → H₀` an inverse system of
`A`-modules with `I ^ (n + 1) H_n = 0`. Suppose a finite family `f_l ∈ I` acts by *up maps*
`u_l : H_n → H_{n+1}` whose composite with the transition is multiplication by `f_l`, and that
there are *obstruction maps* `δ_n : H_n → O_n` such that

* an element with vanishing obstruction lifts to every later level;
* the obstructions intertwine the up maps with maps `μ_l : O_n → O_{n+1}`;
* the elements coming from far enough up have obstructions in submodules `P_n ⊆ O_n`, stable under
  the `μ_l`, inside which every `μ`-stable family of `I`-power torsion submodules is eventually
  generated in degree one.

Then the system `(H_n)` satisfies the Mittag-Leffler condition.

## Main results

* `Stacks.Cohomology.EventualLifting.exists_sub_mem_pow_smul`: for `z ∈ δ_{c+k}⁻¹(P_{c+k})` and
  `i ≤ c`, the image of `z` in `H_i` agrees, modulo `I ^ k H_i`, with the image of an element of
  vanishing obstruction.
* `Stacks.Cohomology.EventualLifting.isMittagLefflerCategorical_of_eventualLifting`: the
  Mittag-Leffler condition from such a family of obstructions.

## References

* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.Cohomology.EventualLifting

variable {A : Type u} [CommRing A] (H : ℕᵒᵖ ⥤ ModuleCat.{v} A)

/-- The transition map of `H` from level `m` down to level `n`, as a linear map. -/
abbrev trans {n m : ℕ} (h : n ≤ m) : H.obj (op m) →ₗ[A] H.obj (op n) :=
  (H.map (homOfLE h).op).hom

/-- The transition maps of `H` compose. -/
theorem trans_trans {k n m : ℕ} (h₁ : k ≤ n) (h₂ : n ≤ m) (x : H.obj (op m)) :
    trans H h₁ (trans H h₂ x) = trans H (h₁.trans h₂) x := by
  show (H.map (homOfLE h₂).op ≫ H.map (homOfLE h₁).op).hom x = _
  rw [← H.map_comp]
  rfl

/-- The image of a transition map from a higher level is contained in the image of one from a lower
level. -/
theorem range_trans_antitone {i n m : ℕ} (h₁ : i ≤ n) (h₂ : n ≤ m) :
    LinearMap.range (trans H (h₁.trans h₂)) ≤ LinearMap.range (trans H h₁) := by
  rintro x ⟨y, rfl⟩
  exact ⟨trans H h₂ y, trans_trans H h₁ h₂ y⟩

variable {L : Type*} [Fintype L] (f : L → A) (I : Ideal A)
  (up : L → ∀ n, H.obj (op n) →ₗ[A] H.obj (op (n + 1)))
  {O : ℕ → Type w} [∀ n, AddCommGroup (O n)] [∀ n, Module A (O n)]
  (δ : ∀ n, H.obj (op n) →ₗ[A] O n) (μ : L → ∀ n, O n →ₗ[A] O (n + 1))

omit [Fintype L] in
/-- The image in a lower level of an up map applied to `y` is `f_l` times the image of `y`. -/
theorem trans_up {i n : ℕ} (hup : ∀ l n x, trans H (Nat.le_succ n) (up l n x) = f l • x)
    (hi : i ≤ n) (l : L) (y : H.obj (op n)) :
    trans H (hi.trans (Nat.le_succ n)) (up l n y) = f l • trans H hi y := by
  rw [← trans_trans H hi (Nat.le_succ n), hup, map_smul]

/-- Write `M_n = δ_n⁻¹(P_n)`. If from degree `c` on the obstructions of elements of `M_{n+1}` are
sums of images under the `μ_l` of obstructions of elements of `M_n`, then for `n ≥ c` every element
of `M_{n+1}` is a sum of up maps of elements of `M_n` plus an element of vanishing obstruction. -/
theorem exists_sub_sum_up
    (hδup : ∀ l n x, δ (n + 1) (up l n x) = μ l n (δ n x)) (P : ∀ n, Submodule A (O n))
    (c : ℕ)
    (hc : ∀ n, c ≤ n → ∀ x ∈ ((P (n + 1)).comap (δ (n + 1))).map (δ (n + 1)),
      ∃ y : L → O n, (∀ l, y l ∈ ((P n).comap (δ n)).map (δ n)) ∧ x = ∑ l, μ l n (y l))
    {n : ℕ} (hn : c ≤ n) (z : H.obj (op (n + 1))) (hz : δ (n + 1) z ∈ P (n + 1)) :
    ∃ y : L → H.obj (op n), (∀ l, δ n (y l) ∈ P n) ∧
      δ (n + 1) (z - ∑ l, up l n (y l)) = 0 := by
  obtain ⟨y', hy', hsum⟩ := hc n hn (δ (n + 1) z) ⟨z, hz, rfl⟩
  choose y hyP hyδ using hy'
  refine ⟨y, hyP, ?_⟩
  rw [map_sub, map_sum, hsum, sub_eq_zero]
  exact Finset.sum_congr rfl fun l _ => by rw [hδup, hyδ]

/-- With the hypotheses of `Stacks.Cohomology.EventualLifting.exists_sub_sum_up`, for `i ≤ c` and
`z ∈ M_{c+k}`, the image of `z` in `H_i` is, modulo `I ^ k H_i`, the image of an element of
vanishing obstruction. -/
theorem exists_sub_mem_pow_smul (hfI : ∀ l, f l ∈ I)
    (hup : ∀ l n x, trans H (Nat.le_succ n) (up l n x) = f l • x)
    (hδup : ∀ l n x, δ (n + 1) (up l n x) = μ l n (δ n x)) (P : ∀ n, Submodule A (O n))
    (c : ℕ)
    (hc : ∀ n, c ≤ n → ∀ x ∈ ((P (n + 1)).comap (δ (n + 1))).map (δ (n + 1)),
      ∃ y : L → O n, (∀ l, y l ∈ ((P n).comap (δ n)).map (δ n)) ∧ x = ∑ l, μ l n (y l))
    {i : ℕ} (hi : i ≤ c) :
    ∀ (k : ℕ) (z : H.obj (op (c + k))), δ (c + k) z ∈ P (c + k) →
      ∃ w : H.obj (op (c + k)), δ (c + k) w = 0 ∧
        trans H (hi.trans (Nat.le_add_right c k)) z - trans H (hi.trans (Nat.le_add_right c k)) w ∈
          (I ^ k • ⊤ : Submodule A (H.obj (op i))) := by
  intro k
  induction k with
  | zero =>
    intro z _
    exact ⟨0, map_zero _, by simp⟩
  | succ k ih =>
    intro z hz
    obtain ⟨y, hyP, hy0⟩ := exists_sub_sum_up H up δ μ hδup P c hc
      (n := c + k) (Nat.le_add_right c k) z hz
    choose w hw0 hwr using fun l => ih (y l) (hyP l)
    have hle : i ≤ c + k := hi.trans (Nat.le_add_right c k)
    refine ⟨(z - ∑ l, up l (c + k) (y l)) + ∑ l, up l (c + k) (w l), ?_, ?_⟩
    · show δ (c + k + 1) _ = 0
      rw [map_add, hy0, zero_add, map_sum]
      exact Finset.sum_eq_zero fun l _ => by rw [hδup, hw0, map_zero]
    · have key : ∀ (l : L) (x : H.obj (op (c + k))),
          trans H (hi.trans (Nat.le_add_right c (k + 1))) (up l (c + k) x) =
            f l • trans H hle x := trans_up H f up hup hle
      have hsum : trans H (hi.trans (Nat.le_add_right c (k + 1))) z -
          trans H (hi.trans (Nat.le_add_right c (k + 1)))
            ((z - ∑ l, up l (c + k) (y l)) + ∑ l, up l (c + k) (w l)) =
          ∑ l, f l • (trans H hle (y l) - trans H hle (w l)) := by
        simp only [map_add, map_sub, map_sum, key, smul_sub, Finset.sum_sub_distrib]
        abel
      rw [hsum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [pow_succ', ← smul_smul]
      exact Submodule.smul_mem_smul (hfI l) (hwr l)

/-- **The Mittag-Leffler condition from obstructions that eventually lift.** Here `hup` and `hann`
are the up maps and the annihilation, `hlift` the lifting of elements of vanishing obstruction,
`hδup` the compatibility of the obstructions with the up maps, `hP` and `hgen` the stability and
the eventual generation inside `P_n`, and `hS` that whatever comes from level `e n` has its
obstruction in `P_n`. -/
theorem isMittagLefflerCategorical_of_eventualLifting (hfI : ∀ l, f l ∈ I)
    (hup : ∀ l n x, trans H (Nat.le_succ n) (up l n x) = f l • x)
    (hann : ∀ n, I ^ (n + 1) • (⊤ : Submodule A (H.obj (op n))) = ⊥)
    (hlift : ∀ n x, δ n x = 0 → ∀ m (h : n ≤ m), x ∈ LinearMap.range (trans H h))
    (hδup : ∀ l n x, δ (n + 1) (up l n x) = μ l n (δ n x))
    (P : ∀ n, Submodule A (O n)) (hP : ∀ l n x, x ∈ P n → μ l n x ∈ P (n + 1))
    (hgen : ∀ D : ∀ n, Submodule A (O n), (∀ n, D n ≤ P n) →
      (∀ l n x, x ∈ D n → μ l n x ∈ D (n + 1)) → (∀ n, I ^ (n + 1) • D n = ⊥) →
      ∃ c, ∀ n, c ≤ n → ∀ x ∈ D (n + 1),
        ∃ y : L → O n, (∀ l, y l ∈ D n) ∧ x = ∑ l, μ l n (y l))
    (e : ℕ → ℕ) (he : ∀ n, n ≤ e n)
    (hS : ∀ n x, x ∈ LinearMap.range (trans H (he n)) → δ n x ∈ P n) :
    IsMittagLefflerCategorical H := by
  classical
  let D : ∀ n, Submodule A (O n) := fun n => ((P n).comap (δ n)).map (δ n)
  obtain ⟨c₀, hc₀⟩ := hgen D (fun n => Submodule.map_comap_le _ _)
    (fun l n x hx => by
      obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨up l n s, by
        show δ (n + 1) (up l n s) ∈ P (n + 1)
        rw [hδup]
        exact hP l n _ hs, hδup l n s⟩)
    (fun n => by
      refine le_bot_iff.mp ?_
      show I ^ (n + 1) • ((P n).comap (δ n)).map (δ n) ≤ ⊥
      rw [← Submodule.map_smul'']
      calc _ ≤ (I ^ (n + 1) • (⊤ : Submodule A (H.obj (op n)))).map (δ n) :=
            Submodule.map_mono (Submodule.smul_mono le_rfl le_top)
        _ = ⊥ := by rw [hann n, Submodule.map_bot])
  intro i
  set c := c₀ + i with hcdef
  have hc : ∀ n, c ≤ n → ∀ x ∈ D (n + 1),
      ∃ y : L → O n, (∀ l, y l ∈ D n) ∧ x = ∑ l, μ l n (y l) :=
    fun n hn => hc₀ n (le_trans (Nat.le_add_right c₀ i) hn)
  have hic : i ≤ c := Nat.le_add_left i c₀
  set n := c + (i + 1) with hndef
  have hin : i ≤ n := hic.trans (Nat.le_add_right c (i + 1))
  have hM : ∀ s : H.obj (op n), δ n s ∈ P n → ∀ m (hm : n ≤ m),
      trans H hin s ∈ LinearMap.range (trans H (hin.trans hm)) := by
    intro s hs m hm
    obtain ⟨w, hw0, hwr⟩ := exists_sub_mem_pow_smul H f I up δ μ hfI hup hδup P c hc hic
      (i + 1) s hs
    rw [hann i, Submodule.mem_bot, sub_eq_zero] at hwr
    obtain ⟨v, hv⟩ := hlift n w hw0 m hm
    refine ⟨v, ?_⟩
    rw [hwr, ← hv, trans_trans]
  refine ⟨e n, hin.trans (he n), fun m hm => ?_⟩
  have heq : LinearMap.range (trans H ((hin.trans (he n)).trans hm)) =
      LinearMap.range (trans H (hin.trans (he n))) := by
    refine le_antisymm (range_trans_antitone H (hin.trans (he n)) hm) ?_
    rintro x ⟨y, rfl⟩
    have h := hM _ (hS n _ ⟨y, rfl⟩) m ((he n).trans hm)
    rwa [trans_trans] at h
  show Subobject.mk (image.ι (H.map (homOfLE ((hin.trans (he n)).trans hm)).op)) =
    Subobject.mk (image.ι (H.map (homOfLE (hin.trans (he n))).op))
  have hmk {V W : ModuleCat.{v} A} (g : V ⟶ W) :
      Subobject.mk (image.ι g) =
        Subobject.mk (ModuleCat.ofHom (LinearMap.range g.hom).subtype) :=
    Subobject.mk_eq_mk_of_comm _ _ (ModuleCat.imageIsoRange g)
      (ModuleCat.imageIsoRange_hom_subtype g)
  rw [hmk, hmk]
  show Subobject.mk (ModuleCat.ofHom (LinearMap.range (trans H _)).subtype) =
    Subobject.mk (ModuleCat.ofHom (LinearMap.range (trans H _)).subtype)
  rw [heq]

end Stacks.Cohomology.EventualLifting

end
