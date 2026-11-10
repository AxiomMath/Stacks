module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.RingTheory.Ideal.SymbolicPower

/-!
# The symbolic defect of a prime ideal

The *symbolic defect* of a prime ideal `p` in degree `n` is the image of the symbolic power
`p⁽ⁿ⁾` in the quotient `A / pⁿ`. It measures how far the symbolic power filtration is from the
ordinary power filtration. The defects form an inverse system under the transition maps of the
ordinary powers, and when `p` has dimension one in a Noetherian local ring each defect is an
Artinian module, so the images of the transition maps stabilise.

## Main definitions

* `Ideal.symbolicDefect`: the image of `p⁽ⁿ⁾` in `A / pⁿ`.
* `Ideal.symbolicDefectTransition`: the transition map of the inverse system of defects.
* `Ideal.symbolicDefectTailRange`: the image in the degree `n` defect of the degree `n + k` one.
* `Ideal.symbolicDefectCutoff`: a shift past which the tail ranges no longer shrink.

## Main results

* `Ideal.symbolicDefect_isArtinian`: the defect of a one-dimensional prime over a Noetherian
  local ring is Artinian.
* `Ideal.symbolicDefectTailRange_stabilizes`: the tail ranges stabilise.
* `Ideal.symbolicDefectStableRange_step_surjective`: an element of a stabilised tail range in
  degree `n` lifts to the stable tail range in degree `n + 1`.

## Implementation notes

The dimension of a prime ideal `p` is expressed as the Krull dimension of `A ⧸ p`. The library
has one symbolic power, `Ideal.symbolicPower`; `symbolicPower'` is an abbreviation for it, and
`Ideal.symbolicPower_eq_symbolicPower'` records that, which lets the membership criterion stated
with the latter name be used on the former.

## References

* [Stacks Project, Tag 0EB5](https://stacks.math.columbia.edu/tag/0EB5)
-/

@[expose] public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- The two library spellings of the symbolic power of a prime ideal agree; `symbolicPower'` is
an abbreviation for `Ideal.symbolicPower`, so this holds by definition. -/
theorem symbolicPower_eq_symbolicPower' (p : Ideal A) [p.IsPrime] (n : ℕ) :
    Ideal.symbolicPower p n = symbolicPower' p n :=
  rfl

/-- The symbolic power filtration is decreasing. -/
theorem symbolicPower_antitone (p : Ideal A) [p.IsPrime] {n m : ℕ} (hnm : n ≤ m) :
    Ideal.symbolicPower p m ≤ Ideal.symbolicPower p n :=
  Ideal.comap_mono (Ideal.map_mono (Ideal.pow_le_pow_right hnm))

/-- The symbolic defect of a prime ideal `p` in degree `n`: the image of the symbolic power
`p⁽ⁿ⁾` in the quotient `A ⧸ pⁿ`. -/
abbrev symbolicDefect (p : Ideal A) [p.IsPrime] (n : ℕ) : Ideal (A ⧸ p ^ n) :=
  (Ideal.symbolicPower p n).map (Ideal.Quotient.mk (p ^ n))

/-- The transition map of the inverse system of symbolic defects, induced by the quotient map
`A ⧸ pᵐ → A ⧸ pⁿ` for `n ≤ m`. -/
def symbolicDefectTransition (p : Ideal A) [p.IsPrime] {n m : ℕ} (hnm : n ≤ m) :
    symbolicDefect p m →ₗ[A] symbolicDefect p n := by
  let f : A ⧸ p ^ m →+* A ⧸ p ^ n :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hnm)
  refine
    { toFun := fun x ↦ ⟨f x.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · obtain ⟨a, ha, hax⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (p ^ m))
        Ideal.Quotient.mk_surjective).mp x.2
    rw [← hax, Ideal.Quotient.factor_mk]
    exact Ideal.mem_map_of_mem _ (symbolicPower_antitone p hnm ha)
  · exact fun x y ↦ Subtype.ext (by simp [f])
  · exact fun a x ↦ Subtype.ext (by simp [f, Algebra.smul_def])

/-- The transition maps of the inverse system of symbolic defects compose. -/
theorem symbolicDefectTransition_comp (p : Ideal A) [p.IsPrime]
    {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    symbolicDefectTransition p hnm ∘ₗ symbolicDefectTransition p hml =
      symbolicDefectTransition p (hnm.trans hml) := by
  ext x
  simp [symbolicDefectTransition]

/-- Pointwise form of `Ideal.symbolicDefectTransition_comp`. -/
private theorem symbolicDefectTransition_transition (p : Ideal A) [p.IsPrime]
    {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) (x : symbolicDefect p l) :
    symbolicDefectTransition p hnm (symbolicDefectTransition p hml x) =
      symbolicDefectTransition p (hnm.trans hml) x :=
  LinearMap.congr_fun (symbolicDefectTransition_comp p hnm hml) x

/-- The image in the degree `n` symbolic defect of the degree `n + k` one. -/
def symbolicDefectTailRange (p : Ideal A) [p.IsPrime] (n k : ℕ) :
    Submodule A (symbolicDefect p n) :=
  LinearMap.range (symbolicDefectTransition p (Nat.le_add_right n k))

/-- The tail ranges of a fixed symbolic defect are decreasing in the shift. -/
theorem symbolicDefectTailRange_antitone (p : Ideal A) [p.IsPrime] (n : ℕ) {k l : ℕ}
    (hkl : k ≤ l) : symbolicDefectTailRange p n l ≤ symbolicDefectTailRange p n k := by
  unfold symbolicDefectTailRange
  rw [← symbolicDefectTransition_comp p (Nat.le_add_right n k)
    (show n + k ≤ n + l by omega)]
  exact LinearMap.range_comp_le_range _ _

/-- Every element of a symbolic defect is killed by some element outside `p`. -/
theorem symbolicDefect_exists_smul_eq_zero (p : Ideal A) [p.IsPrime] (n : ℕ)
    (x : symbolicDefect p n) :
    ∃ s : A, s ∉ p ∧ s • (x : A ⧸ p ^ n) = 0 := by
  obtain ⟨y, hy, hxy⟩ :=
    (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (p ^ n))
      Ideal.Quotient.mk_surjective).mp x.2
  obtain ⟨s, hs, hsy⟩ := (mem_symbolicPower_iff p n y).mp hy
  refine ⟨s, hs, ?_⟩
  rwa [← hxy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]

/-- For a one-dimensional prime over a Noetherian local ring, the symbolic defect in positive
degree is supported at the maximal ideal only. -/
theorem symbolicDefect_support_eq_maximal [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (_hn : 0 < n)
    (hp : ringKrullDim (A ⧸ p) = 1) :
    ∀ q : PrimeSpectrum A, q ∈ Module.support A (symbolicDefect p n) →
      q.asIdeal = IsLocalRing.maximalIdeal A := by
  classical
  intro q hq
  obtain ⟨x, hxann⟩ := Module.mem_support_iff_exists_annihilator.mp hq
  have hmem : ∀ s : A, s • (x : A ⧸ p ^ n) = 0 → s ∈ q.asIdeal := fun s hs ↦
    hxann ((Submodule.mem_annihilator_span_singleton _ _).2 (Subtype.ext hs))
  have hpq : p ≤ q.asIdeal := by
    intro a ha
    refine q.isPrime.mem_of_pow_mem n (hmem _ ?_)
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha n)]
  have hpne : q.asIdeal ≠ p := by
    intro hqp
    obtain ⟨s, hs, hsx⟩ := symbolicDefect_exists_smul_eq_zero p n x
    exact hs (hqp ▸ hmem s hsx)
  let qbar : Ideal (A ⧸ p) := q.asIdeal.map (Ideal.Quotient.mk p)
  have hqbarNe : qbar ≠ ⊥ := by
    intro he
    have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk p)) he
    change Ideal.comap (Ideal.Quotient.mk p)
      (q.asIdeal.map (Ideal.Quotient.mk p)) = Ideal.comap (Ideal.Quotient.mk p) ⊥ at hcomap
    rw [Ideal.comap_map_mk hpq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hcomap
    exact hpne hcomap
  have : Ring.KrullDimLE 1 (A ⧸ p) := Ring.krullDimLE_iff.2 hp.le
  have hqMax : q.asIdeal.IsMaximal := by
    simpa [qbar, Ideal.comap_map_mk hpq] using
      Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
        (K := qbar)
        (H := (Ideal.isPrime_map_quotientMk_of_isPrime hpq).isMaximal_of_ne_bot hqbarNe)
  exact IsLocalRing.eq_maximalIdeal hqMax

/-- For a one-dimensional prime over a Noetherian local ring, the symbolic defect in positive
degree is an Artinian module. -/
theorem symbolicDefect_isArtinian [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : 0 < n)
    (hp : ringKrullDim (A ⧸ p) = 1) : IsArtinian A (symbolicDefect p n) := by
  classical
  let M := symbolicDefect p n
  have hsub : Subsingleton (Module.support A M) := by
    refine ⟨fun q r ↦ ?_⟩
    apply Subtype.ext
    apply PrimeSpectrum.ext
    rw [symbolicDefect_support_eq_maximal p n hn hp q.1 q.2,
      symbolicDefect_support_eq_maximal p n hn hp r.1 r.2]
  have hdim : Module.supportDim A M ≤ 0 := by
    change Order.krullDim (Module.support A M) ≤ 0
    rw [Order.krullDim_nonpos_iff_forall_isMax]
    exact fun q r _ ↦ (hsub.elim r q).le
  have hquotdim : Ring.KrullDimLE 0 (A ⧸ Module.annihilator A M) :=
    (Ring.krullDimLE_iff).2 (by rwa [← Module.supportDim_eq_ringKrullDim_quotient_annihilator])
  have : IsArtinianRing (A ⧸ Module.annihilator A M) :=
    (isArtinianRing_iff_krullDimLE_zero).2 hquotdim
  let : Module (A ⧸ Module.annihilator A M) M :=
    Module.quotientAnnihilator (R := A) (M := M)
  have : Module.Finite (A ⧸ Module.annihilator A M) M :=
    Module.Finite.of_restrictScalars_finite A _ _
  exact isArtinian_of_surjective_algebraMap (R := A ⧸ Module.annihilator A M)
    (M := M) Ideal.Quotient.mk_surjective

/-- The tail ranges of a fixed symbolic defect eventually stop shrinking. -/
theorem symbolicDefectTailRange_stabilizes [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : 0 < n)
    (hp : ringKrullDim (A ⧸ p) = 1) :
    ∃ k, ∀ l, k ≤ l → symbolicDefectTailRange p n k = symbolicDefectTailRange p n l := by
  have : IsArtinian A (symbolicDefect p n) := symbolicDefect_isArtinian p n hn hp
  let f : ℕ →o (Submodule A (symbolicDefect p n))ᵒᵈ :=
    ⟨fun k ↦ OrderDual.toDual (symbolicDefectTailRange p n k), fun k l hkl ↦
      symbolicDefectTailRange_antitone p n hkl⟩
  obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes f
  exact ⟨k, fun l hkl ↦ congrArg OrderDual.ofDual (hk l hkl)⟩

/-- A shift past which the tail ranges of the degree `n` symbolic defect no longer shrink. -/
noncomputable def symbolicDefectCutoff [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : 0 < n)
    (hp : ringKrullDim (A ⧸ p) = 1) : ℕ :=
  Classical.choose (symbolicDefectTailRange_stabilizes p n hn hp)

/-- Beyond `Ideal.symbolicDefectCutoff` the tail ranges are all equal. -/
theorem symbolicDefectCutoff_spec [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal A) [p.IsPrime] (n : ℕ) (hn : 0 < n)
    (hp : ringKrullDim (A ⧸ p) = 1) (l : ℕ)
    (hl : symbolicDefectCutoff p n hn hp ≤ l) :
    symbolicDefectTailRange p n (symbolicDefectCutoff p n hn hp) =
      symbolicDefectTailRange p n l :=
  (Classical.choose_spec (symbolicDefectTailRange_stabilizes p n hn hp)) l hl

/-- An element of a stabilised tail range in degree `n` is the image of an element of the tail
range in degree `n + 1`. -/
theorem symbolicDefectStableRange_step_surjective
    (p : Ideal A) [p.IsPrime] (n Nn Nnext : ℕ)
    (hn : ∀ k, Nn ≤ k → symbolicDefectTailRange p n Nn =
      symbolicDefectTailRange p n k)
    (x : symbolicDefect p n) (hx : x ∈ symbolicDefectTailRange p n Nn) :
    ∃ y : symbolicDefect p (n + 1),
      y ∈ symbolicDefectTailRange p (n + 1) Nnext ∧
      symbolicDefectTransition p (Nat.le_succ n) y = x := by
  rw [hn (Nn + Nnext + 1) (by omega)] at hx
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
  refine ⟨symbolicDefectTransition p (Nat.le_add_right (n + 1) Nnext)
      (symbolicDefectTransition p (by omega : n + 1 + Nnext ≤ n + (Nn + Nnext + 1)) z),
    LinearMap.mem_range_self _ _, ?_⟩
  rw [symbolicDefectTransition_transition, symbolicDefectTransition_transition]

end Ideal
