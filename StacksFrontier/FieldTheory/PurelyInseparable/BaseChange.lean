module

import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.SeparablyGenerated

public import StacksFrontier.FieldTheory.TranscendentalSeparable
public import StacksFrontier.FieldTheory.Separable.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purely inseparable base change to a separable extension

Let `K/k` be a finitely generated field extension. Then there is a commutative square of field
extensions
```
K  →  K'
↑     ↑
k  →  k'
```
in which `k'/k` and `K'/K` are finite purely inseparable and `K'/k'` is separably generated.
Inside a perfect field extension `Ω/K` the square can moreover be chosen with `K'` the compositum
`k'K` and `K' = (k' ⊗[k] K)_red`, and with `K'/k'` separable in the sense of [stacks, 030O](2),
i.e. each of its finitely generated subextensions has a separating transcendence basis.

## Main definitions

* `Stacks04KMConclusion`: the existence of such a square with `K'/k'` separably generated.

## Main results

* `exists_purelyInseparable_separablyGenerated_of_fg`: a finitely generated field extension
  becomes separably generated after a finite purely inseparable base change.
* `exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType`: the square exists inside
  any perfect field extension `Ω/K`, with `K' = k'K` and `K' = (k' ⊗[k] K)_red`.

## Implementation notes

Separability of `K'/k'` in `exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType`
is `Algebra.IsSeparableExtension`, the notion of [stacks, 030O](2), and not Mathlib's
`Algebra.IsSeparable`: the latter forces algebraicity, while `K'/k'` is in general transcendental.

`K/k` finitely generated as a field extension is `Algebra.EssFiniteType k K`
(`IntermediateField.fg_top_iff`); `Algebra.FiniteType k K` would be the strictly stronger
"finitely generated as an algebra".

The identification `K' = (k' ⊗[k] K)_red` is stated for the canonical map
`Algebra.TensorProduct.productMap`, `x ⊗ y ↦ xy`, as surjectivity together with
`RingHom.ker = nilradical`.

## References

* [Stacks Project, Tag 04KM](https://stacks.math.columbia.edu/tag/04KM)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
-/

@[expose] public section

@[expose] public section

/-- There is a commutative square of field extensions `k → k' → K'`, `k → K → K'` with `k'/k`
and `K'/K` finite purely inseparable and `K'/k'` separably generated. -/
def Stacks04KMConclusion (k K : Type) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ (k' K' : Type) (_ : Field k') (_ : Field K')
    (_ : Algebra k k') (_ : Algebra k' K') (_ : Algebra K K'),
    (algebraMap k' K').comp (algebraMap k k') = (algebraMap K K').comp (algebraMap k K) ∧
    (IsPurelyInseparable k k' ∧ Module.Finite k k') ∧
    (IsPurelyInseparable K K' ∧ Module.Finite K K') ∧
    SeparablyGenerated k' K'

/-- If `K/k` is separably generated, then `Stacks04KMConclusion k K` holds, with `k' = k` and
`K' = K`. -/
theorem separablyGeneratedSquare_of_separablyGenerated
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (h : SeparablyGenerated k K) : Stacks04KMConclusion k K := by
  refine ⟨k, K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩, h⟩
  ext x; simp

/-- If the base field `k` is perfect and `K/k` is finitely generated, then
`Stacks04KMConclusion k K` holds, with `k' = k` and `K' = K`. -/
theorem exists_purelyInseparable_separablyGenerated_of_perfectField
    (k K : Type) [Field k] [Field K] [Algebra k K] [PerfectField k]
    (hfg : (⊤ : IntermediateField k K).FG) : Stacks04KMConclusion k K := by
  have hess : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  apply separablyGeneratedSquare_of_separablyGenerated
  obtain ⟨s, hbasis, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  refine ⟨s, ((↑) : s → K), hbasis, ?_⟩
  rwa [show Set.range ((↑) : s → K) = (s : Set K) from Subtype.range_coe]

/-- Let `K/k` be finitely generated, and let `k → kp → Kp`, `k → K → Kp` be a commutative square
of fields in which `Kp` is generated over `K` by the image of `kp`. Then `Kp/kp` is essentially
of finite type. -/
theorem finite_descent_essFiniteType
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (kp Kp : Type) [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    (hcomm : (algebraMap kp Kp).comp (algebraMap k kp)
        = (algebraMap K Kp).comp (algebraMap k K))
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap kp Kp)) = ⊤) :
    Algebra.EssFiniteType kp Kp := by
  classical
  rw [← IntermediateField.fg_top_iff]
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t.image (algebraMap K Kp), ?_⟩
  set L : IntermediateField kp Kp :=
    IntermediateField.adjoin kp ↑(t.image (algebraMap K Kp)) with hL
  have hgenL : ∀ x ∈ t, algebraMap K Kp x ∈ L := fun x hx =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
  have hkpL : Set.range (algebraMap kp Kp) ⊆ (L.toSubfield : Set Kp) := by
    rintro _ ⟨x, rfl⟩
    exact L.algebraMap_mem x
  have hKL : Set.range (algebraMap K Kp) ⊆ (L.toSubfield : Set Kp) := by
    rintro _ ⟨x, rfl⟩
    set M : Subfield K := L.toSubfield.comap (algebraMap K Kp) with hM
    have hsub : (IntermediateField.adjoin k ↑t).toSubfield ≤ M := by
      apply IntermediateField.adjoin_le_subfield
      · rintro _ ⟨y, rfl⟩
        simp only [SetLike.mem_coe, hM, Subfield.mem_comap]
        have hval : algebraMap K Kp (algebraMap k K y)
            = algebraMap kp Kp (algebraMap k kp y) := (RingHom.congr_fun hcomm y).symm
        rw [hval]
        exact L.algebraMap_mem _
      · intro x hx
        simp only [SetLike.mem_coe, hM, Subfield.mem_comap]
        exact hgenL x hx
    rw [ht] at hsub
    have hx : x ∈ M := hsub (by trivial)
    rwa [hM, Subfield.mem_comap] at hx
  have hle : (⊤ : IntermediateField K Kp).toSubfield ≤ L.toSubfield := by
    rw [← hgen]
    exact IntermediateField.adjoin_le_subfield K _ hKL hkpL
  have htop : L.toSubfield = ⊤ :=
    le_antisymm le_top (le_trans (fun x _ => Subfield.mem_top x) hle)
  apply IntermediateField.toSubfield_injective
  rw [htop]
  rfl

/-- If `Kp/K` is purely inseparable, then for every finite `T ⊆ Kp` the extension `K⟮T⟯/K` is
finite and purely inseparable. -/
theorem finite_descent_adjoin_finite_pi
    {K Kp : Type} [Field K] [Field Kp] [Algebra K Kp]
    (p : ℕ) [ExpChar K p]
    (hKi : IsPurelyInseparable K Kp) (T : Finset Kp) :
    Module.Finite K (IntermediateField.adjoin K (↑T : Set Kp)) ∧
    IsPurelyInseparable K (IntermediateField.adjoin K (↑T : Set Kp)) := by
  have hint : ∀ x ∈ (↑T : Set Kp), IsIntegral K x := fun x _ => hKi.isIntegral.isIntegral x
  refine ⟨?_, ?_⟩
  · have : FiniteDimensional K (IntermediateField.adjoin K (↑T : Set Kp)) :=
      IntermediateField.finiteDimensional_adjoin hint
    infer_instance
  · rw [IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem K Kp p]
    intro x _
    exact IsPurelyInseparable.pow_mem K p x

/-- Finitely many elements of `adjoin K (range (algebraMap kp Kp))` all lie in
`adjoin K ↑T` for a single finite `T ⊆ range (algebraMap kp Kp)`. -/
theorem finite_descent_exists_finset_range
    {K Kp : Type} [Field K] [Field Kp] [Algebra K Kp]
    {kp : Type} [Field kp] [Algebra kp Kp]
    (Δ : Finset Kp)
    (hΔ : ∀ x ∈ Δ, x ∈ IntermediateField.adjoin K (Set.range (algebraMap kp Kp))) :
    ∃ T : Finset Kp, (↑T : Set Kp) ⊆ Set.range (algebraMap kp Kp) ∧
      ∀ x ∈ Δ, x ∈ IntermediateField.adjoin K (↑T : Set Kp) := by
  classical
  have hchoose : ∀ x ∈ Δ, ∃ T : Finset Kp,
      (↑T : Set Kp) ⊆ Set.range (algebraMap kp Kp) ∧
      x ∈ IntermediateField.adjoin K (↑T : Set Kp) := fun x hx =>
    IntermediateField.exists_finset_of_mem_adjoin (hΔ x hx)
  choose T hT1 hT2 using hchoose
  refine ⟨Δ.attach.biUnion (fun x => T x.val x.property), ?_, ?_⟩
  · intro y hy
    simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Set.iUnion_true,
      Set.mem_iUnion] at hy
    obtain ⟨x, hx⟩ := hy
    exact hT1 x.val x.property hx
  · intro x hx
    have hsub : (↑(T x hx) : Set Kp) ⊆ ↑(Δ.attach.biUnion (fun y => T y.val y.property)) := by
      intro y hy
      simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_attach, Set.iUnion_true,
        Set.mem_iUnion]
      exact ⟨⟨x, hx⟩, hy⟩
    exact IntermediateField.adjoin.mono K _ _ hsub (hT2 x hx)

/-- The structure map `algebraMap kp Kp` restricts to a ring homomorphism between
the descended intermediate fields `adjoin k C → adjoin K T`, provided it maps
`adjoin k C` into `adjoin K T`. -/
def finite_descent_inclusionHom
    {k K kp Kp : Type} [Field k] [Field K] [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    (C : Set kp) (T : Set Kp)
    (hmap : ∀ a ∈ IntermediateField.adjoin k C, algebraMap kp Kp a ∈ IntermediateField.adjoin K T) :
    (IntermediateField.adjoin k C) →+* (IntermediateField.adjoin K T) where
  toFun := fun a => ⟨algebraMap kp Kp a.val, hmap a.val a.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- In a commutative square `k → kp → Kp`, `k → K → Kp`, if `algebraMap kp Kp` sends every
element of a finite set `C ⊆ kp` into `K⟮T⟯`, then it sends all of `k⟮C⟯` into `K⟮T⟯`. -/
theorem finite_descent_core_adjoin_subset
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (kp Kp : Type) [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    (hcomm : (algebraMap kp Kp).comp (algebraMap k kp)
        = (algebraMap K Kp).comp (algebraMap k K))
    (C : Finset kp) (T : Finset Kp)
    (hCT : ∀ c ∈ C, algebraMap kp Kp c ∈ IntermediateField.adjoin K (↑T : Set Kp)) :
    ∀ a ∈ IntermediateField.adjoin k (↑C : Set kp),
      algebraMap kp Kp a ∈ IntermediateField.adjoin K (↑T : Set Kp) := by
  intro a ha
  induction ha using IntermediateField.adjoin_induction with
  | mem x hx => exact hCT x (by exact_mod_cast hx)
  | algebraMap r =>
      have hval : algebraMap kp Kp (algebraMap k kp r)
          = algebraMap K Kp (algebraMap k K r) := RingHom.congr_fun hcomm r
      rw [hval]
      exact (IntermediateField.adjoin K (↑T : Set Kp)).algebraMap_mem (algebraMap k K r)
  | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
  | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx

/-- Let `k → kp → Kp`, `k → K → Kp` be a commutative square of fields and let `C ⊆ kp`,
`T ⊆ Kp` be finite sets such that `algebraMap kp Kp` maps `k₁ := k⟮C⟯` into `K₁ := K⟮T⟯`. If
`k₁/k` and `K₁/K` are finite purely inseparable and `K₁/k₁` is separably generated for the
induced algebra structure, then `Stacks04KMConclusion k K` holds. -/
theorem finite_descent_core_conclusion
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p] [ExpChar K p]
    (kp Kp : Type) [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    (hcomm : (algebraMap kp Kp).comp (algebraMap k kp)
        = (algebraMap K Kp).comp (algebraMap k K))
    (C : Finset kp) (T : Finset Kp)
    (hCT : ∀ a ∈ IntermediateField.adjoin k (↑C : Set kp),
      algebraMap kp Kp a ∈ IntermediateField.adjoin K (↑T : Set Kp))
    (hk1fin : Module.Finite k (IntermediateField.adjoin k (↑C : Set kp)))
    (hk1pi : IsPurelyInseparable k (IntermediateField.adjoin k (↑C : Set kp)))
    (hK1fin : Module.Finite K (IntermediateField.adjoin K (↑T : Set Kp)))
    (hK1pi : IsPurelyInseparable K (IntermediateField.adjoin K (↑T : Set Kp)))
    (hsgK1 : @SeparablyGenerated (IntermediateField.adjoin k (↑C : Set kp))
        (IntermediateField.adjoin K (↑T : Set Kp)) _ _
        (finite_descent_inclusionHom (↑C : Set kp) (↑T : Set Kp) hCT).toAlgebra) :
    Stacks04KMConclusion k K := by
  let : Algebra (IntermediateField.adjoin k (↑C : Set kp))
      (IntermediateField.adjoin K (↑T : Set Kp)) :=
    (finite_descent_inclusionHom (↑C : Set kp) (↑T : Set Kp) hCT).toAlgebra
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, _, inferInstance, ?_,
    ⟨hk1pi, hk1fin⟩, ⟨hK1pi, hK1fin⟩, hsgK1⟩
  exact RingHom.ext fun x => Subtype.ext (RingHom.congr_fun hcomm x)

/-- If `Kp/K` is purely inseparable, then for every finite `T ⊆ Kp` the extension `K⟮T⟯/K` is
essentially of finite type. -/
theorem finite_descent_relative_essFiniteType
    {K Kp : Type} [Field K] [Field Kp] [Algebra K Kp]
    (hKi : IsPurelyInseparable K Kp) (T : Finset Kp) :
    Algebra.EssFiniteType K (IntermediateField.adjoin K (↑T : Set Kp)) := by
  have halg : ∀ x ∈ (↑T : Set Kp), IsAlgebraic K x := fun x _ =>
    (hKi.isIntegral.isIntegral x).isAlgebraic
  have heq : (IntermediateField.adjoin K (↑T : Set Kp)).toSubalgebra
      = Algebra.adjoin K (↑T : Set Kp) :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := (↑T : Set Kp)) halg
  have hft : (IntermediateField.adjoin K (↑T : Set Kp)).toSubalgebra.FG := by
    rw [heq]; exact Subalgebra.fg_adjoin_finset T
  have : Algebra.FiniteType K (IntermediateField.adjoin K (↑T : Set Kp)) :=
    ⟨(Subalgebra.fg_top _).mpr hft⟩
  exact Algebra.EssFiniteType.of_finiteType K _

/-- If `γ : M` is separable over `F` and `L` is an intermediate field of `M/F` contained in
`F⟮γ⟯`, then `L/F` is separable. -/
theorem isSeparable_subfield_of_le_adjoin_separable
    (F M : Type) [Field F] [Field M] [Algebra F M]
    (γ : M) (hγ : IsSeparable F γ)
    (L : IntermediateField F M) (hL : L ≤ IntermediateField.adjoin F {γ}) :
    Algebra.IsSeparable F L := by
  have : Algebra.IsSeparable F (IntermediateField.adjoin F {γ}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F M).mpr hγ
  rw [Algebra.isSeparable_def]
  intro x
  have hx : (x : M) ∈ IntermediateField.adjoin F {γ} := hL x.property
  have h1 : IsSeparable F ((⟨(x : M), hx⟩ : IntermediateField.adjoin F {γ})) :=
    Algebra.IsSeparable.isSeparable F _
  have key : minpoly F x = minpoly F (x : M) :=
    (minpoly.algebraMap_eq (algebraMap L M).injective x).symm
  have key2 : minpoly F ((⟨(x : M), hx⟩ : IntermediateField.adjoin F {γ}))
      = minpoly F (x : M) :=
    (minpoly.algebraMap_eq (algebraMap (IntermediateField.adjoin F {γ}) M).injective
      ⟨(x : M), hx⟩).symm
  unfold IsSeparable at h1 ⊢
  rw [key, ← key2]; exact h1

/-- Let `K/k` be finitely generated of exponential characteristic `p`, and let
`k → kp → Kp`, `k → K → Kp` be a commutative square of fields with `kp` perfect, `kp/k` and
`Kp/K` purely inseparable, `Kp/kp` essentially of finite type and `Kp` generated over `K` by the
image of `kp`. Then there are finite sets `C ⊆ kp` and `T ⊆ Kp` such that `algebraMap kp Kp`
maps `k₁ := k⟮C⟯` into `K₁ := K⟮T⟯`, the extensions `k₁/k` and `K₁/K` are finite purely
inseparable, and `K₁/k₁` is separably generated. -/
theorem finite_descent_separablyGenerated
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p] [ExpChar K p]
    (hfg : (⊤ : IntermediateField k K).FG)
    (kp Kp : Type) [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    [PerfectField kp] [Algebra.EssFiniteType kp Kp]
    (hcomm : (algebraMap kp Kp).comp (algebraMap k kp)
        = (algebraMap K Kp).comp (algebraMap k K))
    (hki : IsPurelyInseparable k kp)
    (hKi : IsPurelyInseparable K Kp)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap kp Kp)) = ⊤) :
    ∃ (C : Finset kp) (T : Finset Kp)
      (hCT : ∀ a ∈ IntermediateField.adjoin k (↑C : Set kp),
        algebraMap kp Kp a ∈ IntermediateField.adjoin K (↑T : Set Kp)),
      Module.Finite k (IntermediateField.adjoin k (↑C : Set kp)) ∧
      IsPurelyInseparable k (IntermediateField.adjoin k (↑C : Set kp)) ∧
      Module.Finite K (IntermediateField.adjoin K (↑T : Set Kp)) ∧
      IsPurelyInseparable K (IntermediateField.adjoin K (↑T : Set Kp)) ∧
      @SeparablyGenerated (IntermediateField.adjoin k (↑C : Set kp))
          (IntermediateField.adjoin K (↑T : Set Kp)) _ _
          (finite_descent_inclusionHom (↑C : Set kp) (↑T : Set Kp) hCT).toAlgebra := by
  classical
  have base_mono : ∀ (G : Set Kp) (L L' : IntermediateField k kp), L ≤ L' →
      (IntermediateField.adjoin (↥L) G : Set Kp) ⊆ (IntermediateField.adjoin (↥L') G : Set Kp) := by
    intro G L L' hLL x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact IntermediateField.subset_adjoin (↥L') G hy
    | algebraMap r =>
        have h1 : algebraMap (↥L) Kp r = algebraMap kp Kp (r : kp) := by
          rw [IsScalarTower.algebraMap_apply (↥L) kp Kp]; rfl
        rw [h1]
        have h2 : (r : kp) ∈ L' := hLL r.property
        have h3 : algebraMap kp Kp (r : kp) = algebraMap (↥L') Kp ⟨(r:kp), h2⟩ := by
          rw [IsScalarTower.algebraMap_apply (↥L') kp Kp]; rfl
        rw [h3]; exact (IntermediateField.adjoin (↥L') G).algebraMap_mem _
    | add x y hx hy ihx ihy => exact add_mem ihx ihy
    | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
    | inv x hx ihx => exact inv_mem ihx
  have lift : ∀ (G : Set Kp) (x : Kp) (C₀ C₁ : Finset kp), C₀ ⊆ C₁ →
      x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C₀ : Set kp))) G →
      x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C₁ : Set kp))) G :=
    fun G x C₀ C₁ h hx =>
      base_mono G _ _ (IntermediateField.adjoin.mono k _ _ (by exact_mod_cast h)) hx
  have union : ∀ (G : Set Kp) (x y : Kp),
      (∃ C : Finset kp, x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set
          kp))) G) →
      (∃ C : Finset kp, y ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set
          kp))) G) →
      ∃ C : Finset kp, x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set
          kp))) G ∧ y ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set
          kp))) G := by
    rintro G x y ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    exact ⟨C₁ ∪ C₂, lift G x _ _ Finset.subset_union_left h₁,
      lift G y _ _ Finset.subset_union_right h₂⟩
  have extraction : ∀ (G : Set Kp) (x : Kp), x ∈ IntermediateField.adjoin kp G →
      ∃ C : Finset kp, x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set
          kp))) G := by
    intro G x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => exact ⟨∅, IntermediateField.subset_adjoin _ _ hy⟩
    | algebraMap r =>
        refine ⟨{r}, ?_⟩
        have hr : r ∈ IntermediateField.adjoin k ({r} : Set kp) :=
          IntermediateField.subset_adjoin k _ (by simp)
        have h3 : algebraMap kp Kp r
            = algebraMap (↥(IntermediateField.adjoin k ({r}:Set kp))) Kp ⟨r, hr⟩ := by
          rw [IsScalarTower.algebraMap_apply (↥(IntermediateField.adjoin k ({r}:Set kp))) kp Kp];
              rfl
        rw [h3]
        have hcast : (↑({r} : Finset kp) : Set kp) = ({r} : Set kp) := by simp
        rw [hcast]
        exact (IntermediateField.adjoin (↥(IntermediateField.adjoin k ({r}:Set kp)))
            G).algebraMap_mem _
    | add x y hx hy ihx ihy =>
        obtain ⟨C, h1, h2⟩ := union G x y ihx ihy
        exact ⟨C, add_mem h1 h2⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨C, h1, h2⟩ := union G x y ihx ihy
        exact ⟨C, mul_mem h1 h2⟩
    | inv x hx ihx =>
        obtain ⟨C1, h1⟩ := ihx
        exact ⟨C1, inv_mem h1⟩
  obtain ⟨s, hbasis, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField kp Kp
  set F : IntermediateField kp Kp := IntermediateField.adjoin kp (↑s : Set Kp) with hFdef
  have halgF : Algebra.IsAlgebraic F Kp := by
    have h := hbasis.isAlgebraic_field
    have hr : Set.range (Subtype.val : ↥s → Kp) = (↑s : Set Kp) := Subtype.range_coe
    rw [hr] at h; exact h
  have hessF : Algebra.EssFiniteType F Kp := Algebra.EssFiniteType.of_comp kp F Kp
  have hfdF : FiniteDimensional F Kp := Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨γ, hγtop⟩ := Field.exists_primitive_element F Kp
  have hγsepF : IsSeparable F γ := Algebra.IsSeparable.isSeparable F γ
  set g : Polynomial F := minpoly F γ with hgdef
  obtain ⟨t, ht⟩ := hfg
  set G : Set Kp := (↑s : Set Kp) ∪ {γ} with hGdef
  have hGtop : IntermediateField.adjoin kp G = ⊤ := by
    have h := IntermediateField.adjoin_adjoin_left kp (↑s : Set Kp) {γ}
    rw [hγtop] at h
    simp only [IntermediateField.restrictScalars_top] at h
    exact h.symm
  have hmemG : ∀ x : Kp, x ∈ IntermediateField.adjoin kp G := by
    intro x; rw [hGtop]; trivial
  set Δ₀ : Finset Kp := t.image (algebraMap K Kp) with hΔ₀def
  have hext : ∀ x ∈ Δ₀, ∃ C : Finset kp,
      x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set kp))) G :=
    fun x _ => extraction G x (hmemG x)
  choose Cwit hCwit using hext
  set Δs : Finset Kp := g.support.image (fun i => ((g.coeff i : F) : Kp)) with hΔsdef
  have hexts : ∀ x ∈ Δs, ∃ C : Finset kp,
      x ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C : Set kp)))
        (↑s : Set Kp) := by
    intro x hx
    simp only [hΔsdef, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact extraction (↑s : Set Kp) _ (g.coeff i).property
  choose Cwits hCwits using hexts
  set C : Finset kp :=
    (Δ₀.attach.biUnion (fun x => Cwit x.val x.property))
      ∪ (Δs.attach.biUnion (fun x => Cwits x.val x.property)) with hCdef
  set Δsγ : Finset Kp := s ∪ {γ} with hΔsγdef
  have hΔsγrange : ∀ x ∈ Δsγ,
      x ∈ IntermediateField.adjoin K (Set.range (algebraMap kp Kp)) := by
    intro x _; rw [hgen]; trivial
  obtain ⟨T₀, hT₀range, hT₀mem⟩ := finite_descent_exists_finset_range Δsγ hΔsγrange
  have hpre : ∀ w ∈ T₀, ∃ c : kp, algebraMap kp Kp c = w := fun w hw => hT₀range hw
  choose pre hpre' using hpre
  set Cpre : Finset kp := T₀.attach.image (fun w => pre w.val w.property) with hCpredef
  set C' : Finset kp := C ∪ Cpre with hC'def
  have hCC' : (↑C : Set kp) ⊆ (↑C' : Set kp) := by
    intro y hy; simp only [hC'def, Finset.coe_union, Set.mem_union]; exact Or.inl hy
  set T : Finset Kp := C'.image (algebraMap kp Kp) with hTdef
  have hT₀T : (↑T₀ : Set Kp) ⊆ (↑T : Set Kp) := by
    intro w hw
    have hw' : w ∈ T₀ := hw
    simp only [hTdef, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    refine ⟨pre w hw', ?_, hpre' w hw'⟩
    simp only [hC'def, Finset.mem_union, hCpredef, Finset.mem_image, Finset.mem_attach]
    exact Or.inr ⟨⟨w, hw'⟩, True.intro, rfl⟩
  have hT₀adj : IntermediateField.adjoin K (↑T₀ : Set Kp)
      ≤ IntermediateField.adjoin K (↑T : Set Kp) := IntermediateField.adjoin.mono K _ _ hT₀T
  have hsT : ∀ y ∈ s, y ∈ IntermediateField.adjoin K (↑T : Set Kp) := fun y hy =>
    hT₀adj (hT₀mem y (by simp [hΔsγdef, hy]))
  have hγT : γ ∈ IntermediateField.adjoin K (↑T : Set Kp) :=
    hT₀adj (hT₀mem γ (by simp [hΔsγdef]))
  have hfCT : ∀ c ∈ C', algebraMap kp Kp c ∈ IntermediateField.adjoin K (↑T : Set Kp) := by
    intro c hc
    apply IntermediateField.subset_adjoin
    simp only [hTdef, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨c, hc, rfl⟩
  have hTpre : ∀ w ∈ T, ∃ c ∈ C', algebraMap kp Kp c = w := by
    intro w hw
    simpa only [hTdef, Finset.mem_image] using hw
  have hCwit'2 : ∀ y ∈ Δ₀,
      y ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C' : Set kp))) G :=
    fun y hy => lift G y _ _ (((Finset.subset_biUnion_of_mem (fun z : Δ₀ => Cwit z.1 z.2)
      (Finset.mem_attach _ ⟨y, hy⟩)).trans Finset.subset_union_left).trans
        Finset.subset_union_left) (hCwit y hy)
  have hCwitS2 : ∀ y ∈ Δs,
      y ∈ IntermediateField.adjoin (↥(IntermediateField.adjoin k (↑C' : Set kp)))
        (↑s : Set Kp) :=
    fun y hy => lift _ y _ _ (((Finset.subset_biUnion_of_mem (fun z : Δs => Cwits z.1 z.2)
      (Finset.mem_attach _ ⟨y, hy⟩)).trans Finset.subset_union_right).trans
        Finset.subset_union_left) (hCwits y hy)
  have hCT : ∀ a ∈ IntermediateField.adjoin k (↑C' : Set kp),
      algebraMap kp Kp a ∈ IntermediateField.adjoin K (↑T : Set Kp) :=
    finite_descent_core_adjoin_subset k K kp Kp hcomm C' T hfCT
  obtain ⟨hk1fin, hk1pi⟩ := finite_descent_adjoin_finite_pi (K := k) (Kp := kp) p hki C'
  obtain ⟨hK1fin, hK1pi⟩ := finite_descent_adjoin_finite_pi (K := K) (Kp := Kp) p hKi T
  refine ⟨C', T, hCT, hk1fin, hk1pi, hK1fin, hK1pi, ?_⟩
  let : Algebra (↥(IntermediateField.adjoin k (↑C' : Set kp)))
      (↥(IntermediateField.adjoin K (↑T : Set Kp))) :=
    (finite_descent_inclusionHom (↑C' : Set kp) (↑T : Set Kp) hCT).toAlgebra
  set k₁ : IntermediateField k kp := IntermediateField.adjoin k (↑C' : Set kp) with hk1def
  set K₁ : IntermediateField K Kp := IntermediateField.adjoin K (↑T : Set Kp) with hK1def
  set x : (↥s) → (↥K₁) := fun j => ⟨(j : Kp), hsT j.val j.property⟩ with hxdef
  let inst : Algebra (↥k₁) (↥K₁) :=
    (finite_descent_inclusionHom (↑C' : Set kp) (↑T : Set Kp) hCT).toAlgebra
  have hSep : Algebra.IsSeparable (IntermediateField.adjoin (↑k₁) (Set.range x)) ↑K₁ := by
    have halg : ∀ a : ↥k₁,
        ((algebraMap (↥k₁) (↥K₁) a : ↥K₁) : Kp) = algebraMap kp Kp (a : kp) := fun a => rfl
    set F₁ : IntermediateField (↥k₁) (↥K₁) := IntermediateField.adjoin (↥k₁) (Set.range x)
      with hF₁def
    set γ' : (↥K₁) := ⟨γ, hγT⟩ with hγ'def
    have hxval : ∀ j : ↥s, ((x j : ↥K₁) : Kp) = (j : Kp) := fun j => rfl
    have hGsubK₁ : ∀ v : Kp, v ∈ IntermediateField.adjoin (↥k₁) G → v ∈ K₁ := by
      intro v hv
      induction hv using IntermediateField.adjoin_induction with
      | mem w hw =>
          rcases hw with hws | hwγ
          · exact hsT w hws
          · simp only [Set.mem_singleton_iff] at hwγ; rw [hwγ]; exact hγT
      | algebraMap r =>
          rw [IsScalarTower.algebraMap_apply (↥k₁) kp Kp]
          exact hCT (r : kp) r.property
      | add a b _ _ iha ihb => exact add_mem iha ihb
      | mul a b _ _ iha ihb => exact mul_mem iha ihb
      | inv a _ iha => exact inv_mem iha
    have hbridge : ∀ (S : Set Kp) (S' : Set ↥K₁) (hsub : ∀ v : Kp,
        v ∈ IntermediateField.adjoin (↥k₁) S → v ∈ K₁),
        (∀ w (hw : w ∈ S), (⟨w, hsub w (IntermediateField.subset_adjoin _ _ hw)⟩ : ↥K₁) ∈
          IntermediateField.adjoin (↥k₁) S') →
        ∀ v : Kp, ∀ (hv : v ∈ IntermediateField.adjoin (↥k₁) S),
          (⟨v, hsub v hv⟩ : ↥K₁) ∈ IntermediateField.adjoin (↥k₁) S' := by
      intro S S' hsub hS v hv0
      induction hv0 using IntermediateField.adjoin_induction with
      | mem w hw => exact hS w hw
      | algebraMap r =>
          have hval : algebraMap (↥k₁) Kp r = ((algebraMap (↥k₁) (↥K₁) r : ↥K₁) : Kp) := by
            rw [halg r, IsScalarTower.algebraMap_apply (↥k₁) kp Kp]; rfl
          have hzeq : (⟨algebraMap (↥k₁) Kp r, hsub _ (IntermediateField.algebraMap_mem _ r)⟩ :
              ↥K₁) = algebraMap (↥k₁) (↥K₁) r := Subtype.ext hval
          rw [hzeq]
          exact (IntermediateField.adjoin (↥k₁) S').algebraMap_mem r
      | add a b ha hb iha ihb => exact add_mem iha ihb
      | mul a b ha hb iha ihb => exact mul_mem iha ihb
      | inv a ha iha => exact inv_mem iha
    have hKE : ∀ r : K, (algebraMap K (↥K₁) r) ∈
        IntermediateField.adjoin (↥k₁) (Set.range x ∪ {γ'}) := by
      intro r
      have hrtop : r ∈ IntermediateField.adjoin k (↑t : Set K) := by rw [ht]; trivial
      induction hrtop using IntermediateField.adjoin_induction with
      | mem u hu =>
          have huΔ₀ : algebraMap K Kp u ∈ Δ₀ := by
            simp only [hΔ₀def, Finset.mem_image]; exact ⟨u, by exact_mod_cast hu, rfl⟩
          have hG := hCwit'2 _ huΔ₀
          have hbr := hbridge G (Set.range x ∪ {γ'}) hGsubK₁ (fun w hw => by
            rcases hw with hws | hwγ
            · exact IntermediateField.subset_adjoin (↥k₁) _ (Or.inl ⟨⟨w, hws⟩, rfl⟩)
            · exact IntermediateField.subset_adjoin (↥k₁) _ (Or.inr (Subtype.ext hwγ)))
            (algebraMap K Kp u) hG
          have hval : (⟨algebraMap K Kp u, hGsubK₁ _ hG⟩ : ↥K₁) = algebraMap K (↥K₁) u :=
            Subtype.ext rfl
          rwa [hval] at hbr
      | algebraMap a =>
          have he : (algebraMap K (↥K₁)) ((algebraMap k K) a)
              = (algebraMap (↥k₁) (↥K₁)) (algebraMap k (↥k₁) a) := by
            apply Subtype.ext
            have hlhs : ((algebraMap K (↥K₁)) ((algebraMap k K) a) : Kp)
                = (algebraMap kp Kp) ((algebraMap k kp) a) := by
              exact (RingHom.congr_fun hcomm a).symm
            have hrhs : ((algebraMap (↥k₁) (↥K₁)) (algebraMap k (↥k₁) a) : Kp)
                = (algebraMap kp Kp) ((algebraMap k kp) a) := by
              rw [halg]
              rw [IsScalarTower.algebraMap_apply k (↥k₁) kp]
              rfl
            rw [hlhs, hrhs]
          rw [he]
          exact (IntermediateField.adjoin (↥k₁) (Set.range x ∪ {γ'})).algebraMap_mem _
      | add a b _ _ iha ihb => rw [map_add]; exact add_mem iha ihb
      | mul a b _ _ iha ihb => rw [map_mul]; exact mul_mem iha ihb
      | inv a _ iha => rw [map_inv₀]; exact inv_mem iha
    have hLtop : (⊤ : IntermediateField (↥F₁) (↥K₁)) ≤
        IntermediateField.adjoin (↥F₁) {γ'} := by
      have hkey : IntermediateField.adjoin (↥k₁) (Set.range x ∪ {γ'}) = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨y, hyK₁⟩ -
        induction hyK₁ using IntermediateField.adjoin_induction with
        | mem w hw =>
            obtain ⟨c, hc, hcw⟩ := hTpre w (by exact_mod_cast hw)
            have hck : c ∈ k₁ := IntermediateField.subset_adjoin k _ (by exact_mod_cast hc)
            have hwK : w ∈ K₁ := IntermediateField.subset_adjoin K _ (by exact_mod_cast hw)
            have hval : (⟨w, hwK⟩ : ↥K₁) = algebraMap (↥k₁) (↥K₁) ⟨c, hck⟩ := by
              apply Subtype.ext
              rw [halg ⟨c, hck⟩]; exact hcw.symm
            rw [hval]
            exact (IntermediateField.adjoin (↥k₁) (Set.range x ∪ {γ'})).algebraMap_mem _
        | algebraMap r =>
            exact hKE r
        | add a b _ _ iha ihb => exact add_mem iha ihb
        | mul a b _ _ iha ihb => exact mul_mem iha ihb
        | inv a _ iha => exact inv_mem iha
      intro y _
      have hy1 : y ∈ IntermediateField.adjoin (↥k₁) (Set.range x ∪ {γ'}) := by
        rw [hkey]; trivial
      rwa [← IntermediateField.adjoin_adjoin_left (↥k₁) (Set.range x) {γ'}] at hy1
    have hSsubK₁ : ∀ v : Kp, v ∈ IntermediateField.adjoin (↥k₁) (↑s : Set Kp) → v ∈ K₁ := by
      intro v hv
      have hsG : (↑s : Set Kp) ⊆ G := fun z hz => Or.inl hz
      exact hGsubK₁ v (IntermediateField.adjoin.mono (↥k₁) _ _ hsG hv)
    have hbridgeS := hbridge (↑s : Set Kp) (Set.range x) hSsubK₁ fun w hw =>
      IntermediateField.subset_adjoin (↥k₁) _ ⟨⟨w, hw⟩, rfl⟩
    let ι : (↥F₁) →+* Kp := (K₁.subtype).comp (F₁.subtype)
    have hιinj : Function.Injective ι := ι.injective
    set P : Polynomial Kp := g.map (algebraMap (↥F) Kp) with hPdef
    have hgsep : g.Separable := hγsepF
    have hPsep : P.Separable := hgsep.map
    have hcoefflift : ∀ n, P.coeff n ∈ Set.range ι := by
      intro n
      have hceq : P.coeff n = ((g.coeff n : ↥F) : Kp) := by
        rw [hPdef, Polynomial.coeff_map]; rfl
      by_cases hn : n ∈ g.support
      · have hmemΔs : ((g.coeff n : ↥F) : Kp) ∈ Δs := by
          rw [hΔsdef]; exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
        have hadj := hCwitS2 _ hmemΔs
        have hF₁mem := hbridgeS ((g.coeff n : ↥F) : Kp) hadj
        refine ⟨⟨⟨((g.coeff n : ↥F) : Kp), hSsubK₁ _ hadj⟩, hF₁mem⟩, ?_⟩
        rw [hceq]; rfl
      · have hz : P.coeff n = 0 := by
          rw [hceq]
          have hgn : g.coeff n = 0 := by rwa [Polynomial.mem_support_iff, not_not] at hn
          rw [hgn]; simp
        rw [hz]; exact ⟨0, by simp⟩
    have hPlift : P ∈ Polynomial.lifts ι := (Polynomial.lifts_iff_coeff_lifts P).mpr hcoefflift
    obtain ⟨gpoly, hgpoly⟩ := (Polynomial.mem_lifts P).mp hPlift
    have hgpolysep : gpoly.Separable := by
      rw [← Polynomial.separable_map ι, hgpoly]; exact hPsep
    have hroot : (Polynomial.aeval γ') gpoly = 0 := by
      apply K₁.subtype.injective
      rw [map_zero]
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      have hφeq : (K₁.subtype).comp (algebraMap (↥F₁) (↥K₁)) = ι := by
        ext a; rfl
      rw [hφeq]
      show Polynomial.eval₂ ι γ gpoly = 0
      rw [← Polynomial.eval_map, hgpoly]
      rw [hPdef, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact minpoly.aeval (↥F) γ
    have hdvd : minpoly (↥F₁) γ' ∣ gpoly := minpoly.dvd (↥F₁) γ' hroot
    have hsepγ' : IsSeparable (↥F₁) γ' := hgpolysep.of_dvd hdvd
    have hSepTop : Algebra.IsSeparable (↥F₁) (⊤ : IntermediateField (↥F₁) (↥K₁)) :=
      isSeparable_subfield_of_le_adjoin_separable (↥F₁) (↥K₁) γ' hsepγ' ⊤ hLtop
    exact Algebra.IsSeparable.of_algHom (↥F₁) _
      (IntermediateField.topEquiv (F := ↥F₁) (E := ↥K₁)).symm.toAlgHom
  refine ⟨↥s, x, ?_, ?_⟩
  · have hAI_k₁ : AlgebraicIndependent (↥k₁) (Subtype.val : ↥s → Kp) :=
      hbasis.left.restrictScalars (R := ↥k₁) Subtype.val_injective
    let φ : (↥K₁) →ₐ[↥k₁] Kp :=
      { toRingHom := algebraMap (↥K₁) Kp
        commutes' := by
          intro r
          show ((algebraMap (↥k₁) (↥K₁) r : ↥K₁) : Kp) = algebraMap (↥k₁) Kp r
          rw [IsScalarTower.algebraMap_apply (↥k₁) kp Kp]; rfl }
    have hAI_x : AlgebraicIndependent (↥k₁) x := AlgebraicIndependent.of_comp φ hAI_k₁
    rw [hAI_x.isTranscendenceBasis_iff_isAlgebraic]
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp hSep.isAlgebraic
  · exact hSep

/-- Let `K/k` be finitely generated of exponential characteristic `p`, and let
`k → kp → Kp`, `k → K → Kp` be a commutative square of fields with `kp` perfect, `kp/k` and
`Kp/K` purely inseparable, `Kp/kp` essentially of finite type and `Kp` generated over `K` by the
image of `kp`. Then `Stacks04KMConclusion k K` holds. -/
theorem finite_descent_core
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p]
    (hfg : (⊤ : IntermediateField k K).FG)
    (kp Kp : Type) [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    [PerfectField kp] [Algebra.EssFiniteType kp Kp]
    (hcomm : (algebraMap kp Kp).comp (algebraMap k kp)
        = (algebraMap K Kp).comp (algebraMap k K))
    (hki : IsPurelyInseparable k kp)
    (hKi : IsPurelyInseparable K Kp)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap kp Kp)) = ⊤) :
    Stacks04KMConclusion k K := by
  have hExpK : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨C, T, hCT, hk1fin, hk1pi, hK1fin, hK1pi, hsgK1⟩ :=
    finite_descent_separablyGenerated k K p hfg kp Kp hcomm hki hKi hgen
  exact finite_descent_core_conclusion k K p kp Kp hcomm C T hCT
    hk1fin hk1pi hK1fin hK1pi hsgK1

/-- Let `K/k` be finitely generated of exponential characteristic `p`, and let
`k → kp → Kp`, `k → K → Kp` be a commutative square of fields with `kp` perfect, `kp/k` and
`Kp/K` purely inseparable and `Kp` generated over `K` by the image of `kp`. Then
`Stacks04KMConclusion k K` holds. -/
theorem exists_finite_purelyInseparable_separablyGenerated_of_perfectField
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p]
    (hfg : (⊤ : IntermediateField k K).FG)
    (kp Kp : Type) [Field kp] [Field Kp]
    [Algebra k kp] [Algebra kp Kp] [Algebra K Kp]
    [PerfectField kp]
    (hcomm : (algebraMap kp Kp).comp (algebraMap k kp)
        = (algebraMap K Kp).comp (algebraMap k K))
    (hki : IsPurelyInseparable k kp)
    (hKi : IsPurelyInseparable K Kp)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap kp Kp)) = ⊤) :
    Stacks04KMConclusion k K := by
  have hess : Algebra.EssFiniteType kp Kp :=
    finite_descent_essFiniteType k K hfg kp Kp hcomm hgen
  exact finite_descent_core k K p hfg kp Kp hcomm hki hKi hgen

/-- If `k` has exponential characteristic `p` and `K/k` is finitely generated, then
`Stacks04KMConclusion k K` holds. -/
theorem exists_purelyInseparable_separablyGenerated_of_expChar
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [ExpChar k p]
    (hfg : (⊤ : IntermediateField k K).FG) : Stacks04KMConclusion k K := by
  have hExpK : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  let Ω := AlgebraicClosure K
  let kpIF : IntermediateField k Ω := perfectClosure k Ω
  let KpIF : IntermediateField k Ω :=
    kpIF ⊔ IntermediateField.adjoin k (Set.range (algebraMap K Ω))
  have hle : kpIF ≤ KpIF := le_sup_left
  let algKpKp : Algebra (↥kpIF) (↥KpIF) := (IntermediateField.inclusion hle).toAlgebra
  have hKΩ : IntermediateField.adjoin k (Set.range (algebraMap K Ω)) ≤ KpIF := le_sup_right
  have hmemK : ∀ x : K, algebraMap K Ω x ∈ KpIF := fun x =>
    hKΩ (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  let fKKp : K →+* (↥KpIF) :=
    { toFun := fun x => ⟨algebraMap K Ω x, hmemK x⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let algKKp : Algebra K (↥KpIF) := fKKp.toAlgebra
  have hfK : ∀ x : K, (algebraMap K (↥KpIF) x : Ω) = algebraMap K Ω x := fun x => rfl
  have hfkp : ∀ (w : Ω) (hw : w ∈ kpIF),
      ((algebraMap (↥kpIF) (↥KpIF) ⟨w, hw⟩ : ↥KpIF) : Ω) = w := fun w hw => rfl
  have hcomm : (algebraMap (↥kpIF) (↥KpIF)).comp (algebraMap k (↥kpIF))
      = (algebraMap K (↥KpIF)).comp (algebraMap k K) := by
    ext y
    show (algebraMap k (↥kpIF) y : Ω) = algebraMap K Ω (algebraMap k K y)
    rw [← IsScalarTower.algebraMap_apply k K Ω]
    rfl
  have hki : IsPurelyInseparable k (↥kpIF) := inferInstance
  have hKi : IsPurelyInseparable K (↥KpIF) := by
    let Q : IntermediateField k Ω := (perfectClosure K Ω).restrictScalars k
    have hmemQ : ∀ x : Ω, x ∈ Q ↔ x ∈ perfectClosure K Ω := fun x => Iff.rfl
    have h1 : kpIF ≤ Q := by
      intro x hx
      rw [hmemQ, mem_perfectClosure_iff]
      rw [mem_perfectClosure_iff] at hx
      obtain ⟨n, a, ha⟩ := hx
      rw [ringExpChar.eq K p]; rw [ringExpChar.eq k p] at ha
      exact ⟨n, algebraMap k K a, by rw [← ha, ← IsScalarTower.algebraMap_apply k K Ω]⟩
    have h2 : IntermediateField.adjoin k (Set.range (algebraMap K Ω)) ≤ Q := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, hmemQ, mem_perfectClosure_iff]
      exact ⟨0, x, by simp⟩
    have hKpQ : KpIF ≤ Q := sup_le h1 h2
    rw [isPurelyInseparable_iff_pow_mem K p]
    intro x
    have hxQ : (x : Ω) ∈ perfectClosure K Ω := hKpQ x.property
    rw [mem_perfectClosure_iff, ringExpChar.eq K p] at hxQ
    obtain ⟨n, a, ha⟩ := hxQ
    refine ⟨n, a, ?_⟩
    apply Subtype.ext
    show (algebraMap K Ω a) = ((x : ↥KpIF) ^ p ^ n : ↥KpIF).val
    rw [ha]; push_cast; rfl
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap (↥kpIF) (↥KpIF))) = ⊤ := by
    set A : IntermediateField K (↥KpIF) :=
      IntermediateField.adjoin K (Set.range (algebraMap (↥kpIF) (↥KpIF))) with hA
    set B : Subfield Ω := A.toSubfield.map (KpIF.toSubfield.subtype) with hB
    have hkB : ∀ x : k, algebraMap k Ω x ∈ B := by
      intro x
      refine ⟨algebraMap K (↥KpIF) (algebraMap k K x), A.algebraMap_mem _, ?_⟩
      show (algebraMap K Ω (algebraMap k K x)) = algebraMap k Ω x
      rw [← IsScalarTower.algebraMap_apply k K Ω]
    let C : IntermediateField k Ω := B.toIntermediateField hkB
    have hkpC : kpIF ≤ C := by
      intro w hw
      show w ∈ B
      exact ⟨algebraMap (↥kpIF) (↥KpIF) ⟨w, hw⟩,
        IntermediateField.subset_adjoin _ _ ⟨⟨w, hw⟩, rfl⟩, hfkp w hw⟩
    have hadjC : IntermediateField.adjoin k (Set.range (algebraMap K Ω)) ≤ C := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨x, rfl⟩
      show algebraMap K Ω x ∈ B
      refine ⟨algebraMap K (↥KpIF) x, A.algebraMap_mem x, hfK x⟩
    have hKpC : KpIF ≤ C := sup_le hkpC hadjC
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ -
    obtain ⟨a, ha, haz⟩ := hKpC hz
    rwa [← (Subtype.ext haz : a = ⟨z, hz⟩)]
  exact exists_finite_purelyInseparable_separablyGenerated_of_perfectField k K p hfg (↥kpIF) (↥KpIF)
    hcomm hki hKi hgen

/-- Let `K/k` be a finitely generated field extension. Then there are fields `k'` and `K'` with
field homomorphisms `k → k'`, `k' → K'` and `K → K'` such that the square formed with `k → K`
commutes, `k'/k` and `K'/K` are finite purely inseparable, and `K'/k'` is separably generated.
The commutativity of the square is the equality of the composites `k → k' → K'` and
`k → K → K'` of `algebraMap`s. -/
theorem exists_purelyInseparable_separablyGenerated_of_fg
    (k K : Type) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    ∃ (k' K' : Type) (_ : Field k') (_ : Field K')
      (_ : Algebra k k') (_ : Algebra k' K') (_ : Algebra K K'),
      -- commutativity of the square: `k → k' → K'` equals `k → K → K'`
      (algebraMap k' K').comp (algebraMap k k') = (algebraMap K K').comp (algebraMap k K) ∧
      -- (1) `k'/k` finite purely inseparable
      (IsPurelyInseparable k k' ∧ Module.Finite k k') ∧
      -- (2) `K'/K` finite purely inseparable
      (IsPurelyInseparable K K' ∧ Module.Finite K K') ∧
      -- (3) `K'/k'` separably generated
      SeparablyGenerated k' K' := by
  show Stacks04KMConclusion k K
  obtain ⟨q, hq⟩ := ExpChar.exists k
  rcases hq with hq1 | hqp
  · have : CharZero k := charZero_of_expChar_one' k
    exact exists_purelyInseparable_separablyGenerated_of_perfectField k K hfg
  · have : ExpChar k q := ExpChar.prime hqp
    exact exists_purelyInseparable_separablyGenerated_of_expChar k K q hfg

/-! ### Separability after a purely inseparable base change inside a perfect field -/

namespace Stacks.FieldTheory.SeparableBaseChange

open scoped TensorProduct

/-- If `F/k` is a finite purely inseparable extension of exponent `n` and `q` is the exponential
characteristic, then the `q ^ n`-th power of any element of `F ⊗[k] K` comes from `K`. -/
private lemma exists_pow_eq_one_tmul (k F K : Type*) [Field k] [Field F] [CommRing K]
    [Algebra k F] [Algebra k K] [Module.Finite k F] [IsPurelyInseparable k F]
    (q : ℕ) [ExpChar k q] [ExpChar (F ⊗[k] K) q] (x : F ⊗[k] K) :
    ∃ c : K, x ^ q ^ IsPurelyInseparable.exponent k F = (1 : F) ⊗ₜ[k] c := by
  refine TensorProduct.induction_on x ⟨0, ?_⟩ (fun a b => ?_) (fun x y hx hy => ?_)
  · rw [zero_pow (pow_ne_zero _ (expChar_pos k q).ne'), TensorProduct.tmul_zero]
  · obtain ⟨d, hd⟩ := IsPurelyInseparable.exponent_def' k q a
    exact ⟨d • b ^ q ^ IsPurelyInseparable.exponent k F, by
      rw [Algebra.TensorProduct.tmul_pow, ← hd, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]⟩
  · obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [add_pow_expChar_pow, hc, hd, TensorProduct.tmul_add]⟩

/-- For a finite purely inseparable `F/k` and fields `F, K` inside `E` over `k`, the canonical map
`F ⊗[k] K → E` has the nilradical as its kernel: it identifies `(F ⊗[k] K)_red` with the
compositum. -/
private lemma ker_productMap_eq_nilradical (k K E F : Type*) [Field k] [Field K] [Field E]
    [Field F] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [Algebra k F]
    [Algebra F E] [IsScalarTower k F E] [Module.Finite k F] [IsPurelyInseparable k F] :
    RingHom.ker (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F E)
        (IsScalarTower.toAlgHom k K E)) = nilradical (F ⊗[k] K) := by
  set f := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F E)
    (IsScalarTower.toAlgHom k K E) with hf
  obtain ⟨q, _⟩ := ExpChar.exists k
  have hcomp : (f : F ⊗[k] K → E) ∘ algebraMap k (F ⊗[k] K) = algebraMap k E :=
    funext f.commutes
  have : ExpChar (F ⊗[k] K) q :=
    expChar_of_injective_algebraMap (.of_comp (hcomp ▸ (algebraMap k E).injective)) q
  refine le_antisymm (fun x hx => ?_) fun x hx =>
    RingHom.mem_ker.2 ((mem_nilradical.mp hx).map f).eq_zero
  obtain ⟨c, hc⟩ := exists_pow_eq_one_tmul k F K q x
  have h3 : f ((1 : F) ⊗ₜ[k] c) = 0 := by
    rw [← hc, map_pow, RingHom.mem_ker.mp hx, zero_pow (pow_ne_zero _ (expChar_pos k q).ne')]
  have h4 : c = 0 := (algebraMap K E).injective (by simpa [hf] using h3)
  exact mem_nilradical.2 ⟨_, by rw [hc, h4, TensorProduct.tmul_zero]⟩

/-- Being separably generated in the sense of [stacks, 030O](1) depends only on the image of the
base field in the extension: an isomorphism of the base compatible with the two maps into `E`
transports it. -/
private lemma isSeparablyGenerated_of_ringEquiv {L L' E : Type*} [Field L] [Field L'] [Field E]
    [Algebra L E] [Algebra L' E] (i : L ≃+* L')
    (hi : (algebraMap L E : L → E) = (algebraMap L' E) ∘ i)
    [h : Algebra.IsSeparablyGenerated L E] : Algebra.IsSeparablyGenerated L' E := by
  obtain ⟨s, hs, hsep⟩ := h.exists_isTranscendenceBasis_and_isSeparable
  let _ : Algebra L' L := (i.symm : L' →+* L).toAlgebra
  have hmap : (algebraMap L' L : L' → L) = i.symm := rfl
  have : IsScalarTower L' L E := IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, hi]; simp
  let i' : L ≃ₐ[L'] L' := { i with commutes' := fun r => i.apply_symm_apply r }
  refine ⟨s, ((hs.1.restrictScalars
    (hmap ▸ i.symm.injective)).isTranscendenceBasis_iff_isAlgebraic).mpr ?_, ?_⟩
  · have h0 : Algebra.IsAlgebraic
        ↥((Algebra.adjoin L (Set.range ((↑) : s → E))).restrictScalars L') E :=
      hs.1.isTranscendenceBasis_iff_isAlgebraic.mp hs
    rwa [Algebra.restrictScalars_adjoin_of_algEquiv i' hi] at h0
  · have h0 : Algebra.IsSeparable ↥((IntermediateField.adjoin L s).restrictScalars L') E := hsep
    rwa [IntermediateField.restrictScalars_adjoin_of_algEquiv i' hi] at h0

/-- A separably generated extension is separable in the sense of [stacks, 030O](2). -/
private lemma isSeparableExtension_of_isSeparablyGenerated (F E : Type*) [Field F] [Field E]
    [Algebra F E] (h : Algebra.IsSeparablyGenerated F E) : Algebra.IsSeparableExtension F E := by
  obtain ⟨s, hs, hsep⟩ := h.exists_isTranscendenceBasis_and_isSeparable
  refine ⟨fun L _ => ⟨?_⟩⟩
  obtain ⟨t, ht, htsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType
      (k := F) (L := ↥L) (K := E) hs hsep
  exact ⟨(t : Set ↥L), ht, htsep⟩

/-- If an algebraic subextension `F/k` of `E/k` generates `E` over `K` as a field, then the
canonical map `F ⊗[k] K → E`, `x ⊗ y ↦ xy`, is surjective: the compositum is a field, but already
the `k`-subalgebra generated by `K` and `F` is all of `E`. -/
private lemma surjective_productMap_of_adjoin_eq_top {k K E : Type*} [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E] (F : IntermediateField k E)
    [Algebra.IsAlgebraic k ↥F] (h : IntermediateField.adjoin K (F : Set E) = ⊤) :
    Function.Surjective (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom k ↥F E) (IsScalarTower.toAlgHom k K E)) := by
  have hF : (IsScalarTower.toAlgHom k ↥F E).range = Algebra.adjoin k (F : Set E) :=
    (IntermediateField.range_val F).trans (Algebra.adjoin_eq _).symm
  have hK : Algebra.adjoin K (F : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_right K F, h,
      IntermediateField.top_toSubalgebra]
  rw [← AlgHom.range_eq_top, Algebra.TensorProduct.productMap_range, hF, sup_comm,
    ← Algebra.Subalgebra.restrictScalars_adjoin (R := k), hK, Subalgebra.restrictScalars_top]

/-- Cutting a square down to the compositum: for a tower `k → K → K₁ → Ω` and an intermediate
field `k₁` of `K₁/k`, the subextension `K' = K(k₁)` of `K₁/K` contains a copy `k'` of `k₁` and is
generated over `K` by it. -/
private lemma exists_algEquiv_and_adjoin_eq_top (k K Ω : Type*) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    (K₁ : IntermediateField K Ω) (k₁ : IntermediateField k ↥K₁) :
    ∃ (K' : IntermediateField K Ω) (_ : K' ≤ K₁) (k' : IntermediateField k ↥K')
      (e : ↥k₁ ≃ₐ[k] ↥k'), (∀ x : ↥k₁, ((e x : ↥K') : Ω) = ((x : ↥K₁) : Ω)) ∧
        IntermediateField.adjoin K (k' : Set ↥K') = ⊤ := by
  set T : Set Ω := (Subtype.val : ↥K₁ → Ω) '' (k₁ : Set ↥K₁) with hT
  have hmem : ∀ x : ↥k₁, ((x : ↥K₁) : Ω) ∈ IntermediateField.adjoin K T := fun x =>
    IntermediateField.subset_adjoin K T ⟨(x : ↥K₁), x.2, rfl⟩
  let g : ↥k₁ →ₐ[k] ↥(IntermediateField.adjoin K T) :=
    { toFun := fun x => ⟨((x : ↥K₁) : Ω), hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  refine ⟨IntermediateField.adjoin K T,
    IntermediateField.adjoin_le_iff.mpr (by rintro y ⟨z, -, rfl⟩; exact z.2),
    g.fieldRange, AlgEquiv.ofInjectiveField g, fun _ => rfl,
    IntermediateField.lift_injective _ ?_⟩
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  congr 1
  ext y
  simp only [hT, Set.mem_image, SetLike.mem_coe, AlgHom.mem_fieldRange]
  exact ⟨by rintro ⟨z, ⟨x, rfl⟩, rfl⟩; exact ⟨x, x.2, rfl⟩,
    by rintro ⟨z, hz, rfl⟩; exact ⟨g ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩⟩

/-- Let `K/k` be a finitely generated field extension and let `Ω/K` be a perfect field extension.
Then there are intermediate fields `K'` of `Ω/K` and `k'` of `K'/k` with `k'/k` and `K'/K` finite
purely inseparable and `K'/k'` separable in the sense of [stacks, 030O](2), such that `K'` is
generated over `K` by `k'` and the canonical map `k' ⊗[k] K → K'` is surjective with kernel the
nilradical. -/
public theorem solution (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [Algebra K Ω] [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (K' : IntermediateField K Ω) (k' : IntermediateField k ↥K'),
      Module.Finite K ↥K' ∧ IsPurelyInseparable K ↥K' ∧
      Module.Finite k ↥k' ∧ IsPurelyInseparable k ↥k' ∧
      Algebra.IsSeparableExtension ↥k' ↥K' ∧
      IntermediateField.adjoin K (k' : Set ↥K') = ⊤ ∧
      Function.Surjective (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) ∧
      RingHom.ker (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) =
        nilradical (↥k' ⊗[k] K) := by
  obtain ⟨K₁, k₁, _, _, _, _, _⟩ :=
    exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType k K Ω
  obtain ⟨K', hle, k', e, hev, hcompos⟩ := exists_algEquiv_and_adjoin_eq_top k K Ω K₁ k₁
  let _ : Algebra ↥K' ↥K₁ := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K ↥K' ↥K₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra ↥k' ↥K₁ := ((algebraMap ↥K' ↥K₁).comp (algebraMap ↥k' ↥K')).toAlgebra
  have htower : IsScalarTower ↥k' ↥K' ↥K₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite K ↥K' :=
    .of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have : IsPurelyInseparable K ↥K' := .tower_bot K ↥K' ↥K₁
  have : Module.Finite k ↥k' := .equiv e.toLinearEquiv
  have : IsPurelyInseparable k ↥k' := e.isPurelyInseparable
  have : Algebra.IsAlgebraic k ↥k' := .of_finite k ↥k'
  have : Algebra.EssFiniteType k ↥K' := .comp k K ↥K'
  have : Algebra.EssFiniteType ↥k' ↥K' := .of_comp k ↥k' ↥K'
  obtain ⟨s, hs, hsep⟩ :=
    (isSeparablyGenerated_of_ringEquiv (E := ↥K₁) e.toRingEquiv
      (funext fun x => Subtype.ext (hev x).symm)).exists_isTranscendenceBasis_and_isSeparable
  obtain ⟨t, ht, htsep⟩ :=
    @exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType
      ↥k' ↥K₁ ↥K' _ _ _ _ _ _ htower _ s hs hsep
  exact ⟨K', k', ‹_›, ‹_›, ‹_›, ‹_›,
    isSeparableExtension_of_isSeparablyGenerated ↥k' ↥K' ⟨_, ht, htsep⟩, hcompos,
    surjective_productMap_of_adjoin_eq_top k' hcompos,
    ker_productMap_eq_nilradical k K ↥K' ↥k'⟩

end Stacks.FieldTheory.SeparableBaseChange

@[expose] public section

open scoped TensorProduct

/-- Let `K/k` be a finitely generated field extension and let `Ω/K` be a perfect field extension.
Then inside `Ω` there is a diagram
```
K  →  K'
↑     ↑
k  →  k'
```
with `k'/k` and `K'/K` finite purely inseparable and `K'/k'` separable in the sense of
[stacks, 030O](2), in which moreover `K'` is the compositum `k'K` and the canonical map
`k' ⊗[k] K → K'` is surjective with kernel the nilradical, i.e. `K' = (k' ⊗[k] K)_red`. -/
@[stacks 030R, ega "0 19.6.6"]
public theorem exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
    [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (K' : IntermediateField K Ω) (k' : IntermediateField k ↥K'),
      Module.Finite K ↥K' ∧ IsPurelyInseparable K ↥K' ∧
      Module.Finite k ↥k' ∧ IsPurelyInseparable k ↥k' ∧
      Algebra.IsSeparableExtension ↥k' ↥K' ∧
      IntermediateField.adjoin K (k' : Set ↥K') = ⊤ ∧
      Function.Surjective (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) ∧
      RingHom.ker (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom k ↥k' ↥K') (IsScalarTower.toAlgHom k K ↥K')) =
        nilradical (↥k' ⊗[k] K) := by apply Stacks.FieldTheory.SeparableBaseChange.solution

end
