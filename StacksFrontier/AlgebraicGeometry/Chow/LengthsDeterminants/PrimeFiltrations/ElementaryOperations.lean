module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Reindex
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.DimensionLeOne
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Functor
public import StacksFrontier.AlgebraicGeometry.Chow.LengthsDeterminants.GoodSequences
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantOrder
public import StacksCore.Tactic.StacksAttribute

/-!
# Elementary operations on sequences filtered by `R / q`

Let `q` be a prime of a Noetherian local ring. This file collects the elementary facts about
finite sequences in a module used for Tag 02QB: how the prefix spans, admissibility and the
determinant symbol of a sequence change under adding to one entry a combination of its
predecessors, transposing adjacent entries, scaling the entries beyond a cut-off and rescaling
by units; how the localized length at `q` of a prefix span counts its entries; and how
colengths behave along compositions and commutative squares.

## Main results

* `Module.FiniteLength.localized_length_extension`: extending a submodule by one factor
  isomorphic to `R / q` raises the localized length at `q` by one.
* `Module.FiniteLength.localized_length_of_generating`: for a generating sequence whose
  successive factors are `R / q`, the localized length is the number of entries.

## Implementation notes

Successive factors use the same subquotient presentation as Tag 02QC. Localization is
represented by `LocalizedModule`, and an isomorphism of localized modules by bijectivity of
the canonical localized linear map.

`Module.FiniteLength.spanPrefix` indexes the span of an initial segment by a natural number
rather than by an element of `Fin l`, which is what the inductions over the filtration need;
`Module.FiniteLength.spanBefore` is its restriction to a valid index.

## References

* [Stacks Project, Tag 02QB](https://stacks.math.columbia.edu/tag/02QB)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v w

/-- Extending a submodule by one factor isomorphic to `R / q` raises the localized length at
`q` by exactly one: localization is exact and the new factor localizes to the residue field. -/
public theorem localized_length_extension
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    {M : Type v} [AddCommGroup M] [Module R M]
    (U V : Submodule R M) (hUV : U ≤ V)
    (e : (V ⧸ U.submoduleOf V) ≃ₗ[R] R ⧸ q) :
    Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl V) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl U) + 1 := by
  let f : U →ₗ[R] V := Submodule.inclusion hUV
  let g : V →ₗ[R] (V ⧸ U.submoduleOf V) := (U.submoduleOf V).mkQ
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    simpa [Submodule.submoduleOf] using (Submodule.range_inclusion U V hUV).symm
  have hf : Function.Injective f := Submodule.inclusion_injective hUV
  have hg : Function.Surjective g := Submodule.mkQ_surjective _
  have hlocExact := LocalizedModule.map_exact q.primeCompl f g hexact
  have hlocInj := LocalizedModule.map_injective q.primeCompl f hf
  have hlocSurj := LocalizedModule.map_surjective q.primeCompl g hg
  have hlen := Module.length_eq_add_of_exact
    (LocalizedModule.map q.primeCompl f) (LocalizedModule.map q.primeCompl g)
    hlocInj hlocSurj hlocExact
  let e' : LocalizedModule q.primeCompl (V ⧸ U.submoduleOf V) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ q) :=
    LinearEquiv.ofBijective (LocalizedModule.map q.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective q.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective q.primeCompl e.toLinearMap e.surjective⟩
  rwa [e'.length_eq, localized_length_quotient_at_prime_one] at hlen

/-- A map out of a finite module whose only associated prime is `q` is injective as soon as it
is injective after localizing at `q`: the kernel would otherwise have `q` in its support. -/
private theorem injective_of_localized_injective_of_associatedPrimes_subset
    {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (q : Ideal R) [q.IsPrime]
    (φ : M →ₗ[R] N) (hass : associatedPrimes R M ⊆ {q})
    (hφ : Function.Injective (LocalizedModule.map q.primeCompl φ)) : Function.Injective φ := by
  intro x y hxy
  let K := LinearMap.ker φ
  have hxK : x - y ∈ K := by
    change φ (x - y) = 0
    rw [map_sub, hxy, sub_self]
  by_contra hne
  have hK : Nontrivial K :=
    ⟨⟨x - y, hxK⟩, 0, fun heq => hne (sub_eq_zero.mp (congrArg Subtype.val heq))⟩
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R K
  have hpM : p ∈ associatedPrimes R M :=
    associatedPrimes.subset_of_injective (f := K.subtype)
      (Submodule.subtype_injective K) hp
  have hpq : p = q := by simpa using hass hpM
  have hsupport : (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum R) ∈ Module.support R K := by
    rw [Module.mem_support_iff_of_finite, ← Submodule.annihilator_top]
    simpa [hpq] using hp.annihilator_le
  have hlocK : Nontrivial (LocalizedModule q.primeCompl K) :=
    Module.mem_support_iff.mp hsupport
  have hincl : Function.Injective
      (LocalizedModule.map q.primeCompl K.subtype) :=
    LocalizedModule.map_injective q.primeCompl K.subtype
      (Submodule.subtype_injective K)
  have hcomp : (LocalizedModule.map q.primeCompl φ) ∘ₗ
      (LocalizedModule.map q.primeCompl K.subtype) = 0 := by
    ext z
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl K) z
    simp [LocalizedModule.map, IsLocalizedModule.map_mk', K]
  have hzero : LocalizedModule.map q.primeCompl K.subtype = 0 := by
    apply LinearMap.ext
    intro z
    apply hφ
    have hz := congrArg (fun f : _ →ₗ[Localization.AtPrime q] _ => f z) hcomp
    simpa using hz
  have hsub : Subsingleton (LocalizedModule q.primeCompl K) := by
    refine ⟨fun a b => ?_⟩
    apply hincl
    rw [hzero]
    simp
  exact (not_nontrivial_iff_subsingleton.mpr hsub) hlocK

/-- Longer prefixes span larger submodules. -/
private theorem spanPrefix_mono
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {l : ℕ} (x : Fin l → M) {m n : ℕ} (hmn : m ≤ n) :
    spanPrefix (R := R) x m ≤ spanPrefix (R := R) x n :=
  Submodule.span_mono (Set.image_mono fun _ hi => hi.trans_le hmn)

/-- Adding to one entry an element of the span of its predecessors does not change any prefix
span. -/
private theorem spanPrefix_update_add
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {l : ℕ} (x : Fin l → M) (i : Fin l) (t : M)
    (ht : t ∈ spanPrefix (R := R) x i.val) (n : ℕ) :
    spanPrefix (R := R) (Function.update x i (x i + t)) n = spanPrefix (R := R) x n := by
  classical
  let y := Function.update x i (x i + t)
  have hbefore : spanPrefix (R := R) x i.val ≤ spanPrefix (R := R) y i.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := by intro h; subst j; exact (Nat.lt_irrefl _) hj
    exact Submodule.subset_span ⟨j, hj, Function.update_of_ne hji _ _⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · subst j
      rw [Function.update_self]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨i, hj, rfl⟩)
        (spanPrefix_mono x hj.le ht)
    · rw [Function.update_of_ne hji]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · subst j
      have hy : x i + t ∈ spanPrefix (R := R) y n :=
        Submodule.subset_span ⟨i, hj, Function.update_self _ _ _⟩
      have ht' : t ∈ spanPrefix (R := R) y n := spanPrefix_mono y hj.le (hbefore ht)
      change x i ∈ spanPrefix (R := R) y n
      simpa only [add_sub_cancel_right] using Submodule.sub_mem _ hy ht'
    · exact Submodule.subset_span ⟨j, hj, Function.update_of_ne hji _ _⟩

/-- Adding to one entry of an admissible sequence an element of the span of its predecessors
leaves the sequence admissible. -/
private theorem admissible_update_add
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e : AdmissibleSequence R M)
    (i : Fin (moduleLength R M)) (t : M) (ht : t ∈ spanBefore (R := R) e.1 i) :
    IsAdmissibleSequence (R := R) (Function.update e.1 i (e.1 i + t)) := by
  classical
  intro j r hr
  rw [spanBefore_eq_spanPrefix, spanPrefix_update_add e.1 i t ht]
  by_cases hji : j = i
  · subst j
    rw [Function.update_self, smul_add]
    exact Submodule.add_mem _ (e.2 i r hr) (Submodule.smul_mem _ _ ht)
  · rw [Function.update_of_ne hji]
    exact e.2 j r hr

/-- If `e'` is obtained from `e` by replacing the entry `i` with a predecessor-modulo unit
multiple of itself, the symbols differ by the residue of that unit. -/
private theorem symbol_eq_residue_smul_of_update
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e e' : AdmissibleSequence R M)
    (i : Fin (moduleLength R M)) (u : Rˣ) (t : M) (he : e.1 i = (u : R) • e'.1 i + t)
    (ht : t ∈ spanBefore (R := R) e.1 i) (hupd : Function.update e.1 i (e'.1 i) = e'.1) :
    symbol e = IsLocalRing.residue R u • symbol e' := by
  have hadm : IsAdmissibleSequence (R := R) (Function.update e.1 i (e'.1 i)) := by
    rw [hupd]
    exact e'.2
  have h := symbol_unitChange e i u (e'.1 i) t he ht hadm
  rwa [show (⟨_, hadm⟩ : AdmissibleSequence R M) = e' from Subtype.ext hupd] at h

/-- Adding to one entry of an admissible sequence an element of the span of its predecessors
leaves its symbol unchanged. -/
private theorem symbol_update_add
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e : AdmissibleSequence R M)
    (i : Fin (moduleLength R M)) (t : M) (ht : t ∈ spanBefore (R := R) e.1 i) :
    symbol ⟨Function.update e.1 i (e.1 i + t), admissible_update_add e i t ht⟩ = symbol e := by
  classical
  let e' : AdmissibleSequence R M :=
    ⟨Function.update e.1 i (e.1 i + t), admissible_update_add e i t ht⟩
  have h := symbol_eq_residue_smul_of_update e' e i 1 t (by simp [e'])
    (by
      change t ∈ spanPrefix (R := R) (Function.update e.1 i (e.1 i + t)) i.val
      rw [spanPrefix_update_add e.1 i t ht]
      exact ht) (by simp [e', Function.update_idem])
  simpa only [Units.val_one, map_one, one_smul] using h

/-- Transposing two entries that lie on the same side of the cut-off does not change the prefix
span. -/
private theorem spanPrefix_swap
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {l : ℕ} (x : Fin l → M) (a b : Fin l) (n : ℕ)
    (h : a.val < n ↔ b.val < n) :
    spanPrefix (R := R) (x ∘ Equiv.swap a b) n = spanPrefix (R := R) x n := by
  classical
  have hmem (j : Fin l) : (Equiv.swap a b j).val < n ↔ j.val < n := by
    by_cases hja : j = a
    · subst j
      simpa only [Equiv.swap_apply_left] using h.symm
    by_cases hjb : j = b
    · subst j
      simpa only [Equiv.swap_apply_right] using h
    simp only [Equiv.swap_apply_of_ne_of_ne hja hjb]
  unfold spanPrefix
  congr 1
  ext z
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Equiv.swap a b j, (hmem j).mpr hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Equiv.swap a b j, (hmem j).mpr hj, by simp⟩

/-- Transposing two adjacent entries of an admissible sequence leaves it admissible, provided
the later entry is already killed into the span before the earlier one. -/
private theorem admissible_swap_adjacent
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e : AdmissibleSequence R M)
    (a b : Fin (moduleLength R M)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ spanBefore (R := R) e.1 b) :
    IsAdmissibleSequence (R := R) (e.1 ∘ Equiv.swap a b) := by
  classical
  have hbefore : spanPrefix (R := R) (e.1 ∘ Equiv.swap a b) b.val =
      spanPrefix (R := R) e.1 b.val := spanPrefix_swap e.1 a b b.val (by omega)
  intro j r hr
  rw [spanBefore_eq_spanPrefix]
  by_cases hjb : j = b
  · subst j
    rw [Function.comp_apply, Equiv.swap_apply_right, hbefore]
    exact ha r hr
  by_cases hja : j = a
  · subst j
    rw [Function.comp_apply, Equiv.swap_apply_left]
    apply spanPrefix_mono (e.1 ∘ Equiv.swap a b) (by omega : b.val ≤ a.val)
    rw [hbefore]
    exact e.2 b r hr
  have hval : j.val ≠ a.val := fun h => hja (Fin.ext h)
  rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hja hjb,
    spanPrefix_swap e.1 a b j.val (by omega)]
  exact e.2 j r hr

/-- Transposing two adjacent entries of an admissible sequence negates its symbol, under the
same hypothesis. -/
private theorem symbol_swap_adjacent
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e : AdmissibleSequence R M)
    (a b : Fin (moduleLength R M)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ spanBefore (R := R) e.1 b) :
    symbol e = -symbol ⟨e.1 ∘ Equiv.swap a b, admissible_swap_adjacent e a b hba ha⟩ := by
  classical
  have heq : Function.update (Function.update e.1 b (e.1 a)) a (e.1 b) =
      e.1 ∘ Equiv.swap a b := by
    have hab : a ≠ b := by intro h; subst a; omega
    funext j
    by_cases hja : j = a
    · subst j
      simp
    by_cases hjb : j = b
    · subst j
      simp [hab.symm]
    simp [hja, hjb, Equiv.swap_apply_of_ne_of_ne hja hjb]
  have hadm : IsAdmissibleSequence (R := R)
      (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b)) := by
    rw [heq]
    exact admissible_swap_adjacent e a b hba ha
  have h := symbol_swap e a b hba ha hadm
  have he : (⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hadm⟩ :
      AdmissibleSequence R M) =
        ⟨e.1 ∘ Equiv.swap a b, admissible_swap_adjacent e a b hba ha⟩ := Subtype.ext heq
  rw [he] at h
  exact h

/-- Scaling the entries beyond a cut-off can only shrink a prefix span. -/
private theorem spanPrefix_scale_suffix_le
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {l : ℕ} (x : Fin l → M) (a : R) (k n : ℕ) :
    spanPrefix (R := R) (fun i => if i.val < k then x i else a • x i) n ≤
      spanPrefix (R := R) x n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, hi, rfl⟩
  change (if i.val < k then x i else a • x i) ∈ spanPrefix (R := R) x n
  split_ifs
  · exact Submodule.subset_span ⟨i, hi, rfl⟩
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- An element of a prefix span becomes, after scaling, an element of the prefix span of the
sequence whose tail is scaled. -/
private theorem smul_mem_spanPrefix_scale_suffix
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {l : ℕ} (x : Fin l → M) (a : R) (k n : ℕ) {z : M}
    (hz : z ∈ spanPrefix (R := R) x n) :
    a • z ∈ spanPrefix (R := R) (fun i => if i.val < k then x i else a • x i) n := by
  let P := spanPrefix (R := R) (fun i => if i.val < k then x i else a • x i) n
  have h : spanPrefix (R := R) x n ≤ P.comap (a • LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change a • x i ∈ P
    have hxi : (if i.val < k then x i else a • x i) ∈ P :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    by_cases hik : i.val < k
    · rw [ite_eq_left hik] at hxi
      exact P.smul_mem a hxi
    · simpa only [ite_eq_right hik] using hxi
  exact h hz

/-- The localized length of a prefix span is the number of entries in the prefix: each step of
the filtration contributes one. -/
public theorem localized_length_spanPrefix
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    {M : Type v} [AddCommGroup M] [Module R M] {l : ℕ}
    (x : Fin l → M)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (n : ℕ) (hn : n ≤ l) :
    Module.length (Localization.AtPrime q)
      (LocalizedModule q.primeCompl (spanPrefix (R := R) x n)) = n := by
  induction n with
  | zero =>
      have hzero : spanPrefix (R := R) x 0 = (⊥ : Submodule R M) := by simp [spanPrefix]
      have : Subsingleton
          (LocalizedModule q.primeCompl (spanPrefix (R := R) x 0)) := by
        rw [hzero]
        infer_instance
      exact Module.length_eq_zero_iff.mpr inferInstance
  | succ n ih =>
      have hnlt : n < l := by omega
      let i : Fin l := ⟨n, hnlt⟩
      let U : Submodule R M := spanPrefix (R := R) x n
      let V : Submodule R M := U ⊔ R ∙ x i
      have hV : spanPrefix (R := R) x (n + 1) = V := by
        simpa [U, V, i] using spanPrefix_succ x n hnlt
      have hfac : Nonempty ((V ⧸ (U.submoduleOf V)) ≃ₗ[R] R ⧸ q) := by
        have hi : spanBefore (R := R) x i = U := by
          simpa [U, i] using spanBefore_eq_spanPrefix x i
        have hxi := hxf i
        rw [hi] at hxi
        simpa [V, Submodule.submoduleOf] using hxi
      obtain ⟨e⟩ := hfac
      rw [hV, localized_length_extension q U V le_sup_left e, ih (by omega)]
      simp

/-- The localization of a linear equivalence is a linear equivalence of localized modules. -/
public noncomputable def localizedLinearEquiv
    {R : Type u} [CommRing R] (S : Submonoid R)
    {A : Type v} {B : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    LocalizedModule S A ≃ₗ[Localization S] LocalizedModule S B :=
  LinearEquiv.ofBijective (LocalizedModule.map S e.toLinearMap)
    ⟨LocalizedModule.map_injective S e.toLinearMap e.injective,
      LocalizedModule.map_surjective S e.toLinearMap e.surjective⟩

/-- The full prefix of a generating sequence spans everything. -/
private theorem spanPrefix_eq_top_of_generating
    {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    {l : ℕ} (x : Fin l → M) (hx : Submodule.span R (Set.range x) = ⊤) :
    spanPrefix (R := R) x l = ⊤ := by
  unfold spanPrefix
  have hset : x '' {i | i.val < l} = Set.range x := by
    ext z
    simp [Fin.is_lt]
  rw [hset, hx]

/-- For a generating sequence whose successive factors are `R / q`, the localized length of the
module at `q` is the number of entries. -/
public theorem localized_length_of_generating
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    {M : Type v} [AddCommGroup M] [Module R M] {l : ℕ}
    (x : Fin l → M) (hx : Submodule.span R (Set.range x) = ⊤)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q)) :
    Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl M) = l := by
  have hprefix := localized_length_spanPrefix q x hxf l le_rfl
  have htop := spanPrefix_eq_top_of_generating x hx
  let eTop : spanPrefix (R := R) x l ≃ₗ[R] M :=
    (LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv
  rw [← (localizedLinearEquiv q.primeCompl eTop).length_eq]
  exact hprefix

/-- An injective map between modules of the same finite length is surjective. -/
private theorem surjective_of_injective_of_length_eq
    {R : Type u} {M : Type v} {N : Type w} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (hf : Function.Injective f)
    (hM : Module.length R M = n) (hN : Module.length R N = n) :
    Function.Surjective f := by
  let C := N ⧸ LinearMap.range f
  have hlen := Module.length_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)
  rw [hM, hN] at hlen
  have hc_ne_top : Module.length R C ≠ ⊤ := by
    intro hc
    rw [hc] at hlen
    simp at hlen
  have hc_toNat : (Module.length R C).toNat = 0 := by
    have hnat := congrArg ENat.toNat hlen
    rw [ENat.toNat_add (by simp) hc_ne_top] at hnat
    simp only [ENat.toNat_natCast] at hnat
    omega
  have hc_zero : Module.length R C = 0 :=
    (ENat.toNat_eq_zero.mp hc_toNat).resolve_right hc_ne_top
  have hC : Subsingleton C := Module.length_eq_zero_iff.mp hc_zero
  intro y
  have hz : (LinearMap.range f).mkQ y = 0 := Subsingleton.elim _ _
  exact LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hz)

/-- Colengths add along a composition whose second factor is injective. -/
private theorem length_coker_comp_of_injective
    {R : Type*} [Ring R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R (C ⧸ LinearMap.range (g.comp f)) =
      Module.length R (B ⧸ LinearMap.range f) +
        Module.length R (C ⧸ LinearMap.range g) := by
  let S := LinearMap.range (g.comp f)
  let T := LinearMap.range g
  have hS : S = (LinearMap.range f).map g := LinearMap.range_comp f g
  have hST : S ≤ T := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, rfl⟩
  let i := (LinearMap.range f).mapQ S g (by
    rw [hS]
    intro b hb
    exact ⟨b, hb, rfl⟩)
  let p := S.mapQ T LinearMap.id (by simpa using hST)
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hS,
      Submodule.comap_map_eq_of_injective hg, Submodule.mkQ_map_self]
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective T z
    exact ⟨S.mkQ c, rfl⟩
  have hrange : LinearMap.range i = T.map S.mkQ :=
    Submodule.range_mapQ _ _ _ _
  exact Module.length_eq_add_of_exact i p hi hp (by
    rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_id, hrange])

/-- In a commutative square with both vertical maps injective, the two ways of computing the
colength of the composite agree. -/
private theorem length_coker_commutative_square
    {R : Type*} [Ring R] {A B C D : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (i : A →ₗ[R] B) (j : C →ₗ[R] D) (f : A →ₗ[R] C) (g : B →ₗ[R] D)
    (hj : Function.Injective j) (hg : Function.Injective g)
    (hcomm : j.comp f = g.comp i) :
    Module.length R (C ⧸ LinearMap.range f) +
        Module.length R (D ⧸ LinearMap.range j) =
      Module.length R (B ⧸ LinearMap.range i) +
        Module.length R (D ⧸ LinearMap.range g) := by
  rw [← length_coker_comp_of_injective f j hj, hcomm,
    length_coker_comp_of_injective i g hg]

/-- The same identity as an equation of integers, once all four colengths are finite. -/
private theorem length_coker_commutative_square_toInt
    {R : Type*} [Ring R] {A B C D : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (i : A →ₗ[R] B) (j : C →ₗ[R] D) (f : A →ₗ[R] C) (g : B →ₗ[R] D)
    (hj : Function.Injective j) (hg : Function.Injective g)
    (hcomm : j.comp f = g.comp i)
    (hi : IsFiniteLength R (B ⧸ LinearMap.range i))
    (hj' : IsFiniteLength R (D ⧸ LinearMap.range j))
    (hf : IsFiniteLength R (C ⧸ LinearMap.range f))
    (hg' : IsFiniteLength R (D ⧸ LinearMap.range g)) :
    ((Module.length R (C ⧸ LinearMap.range f)).toNat : ℤ) +
        ((Module.length R (D ⧸ LinearMap.range j)).toNat : ℤ) =
      ((Module.length R (B ⧸ LinearMap.range i)).toNat : ℤ) +
        ((Module.length R (D ⧸ LinearMap.range g)).toNat : ℤ) := by
  have h := congrArg ENat.toNat (length_coker_commutative_square i j f g hj hg hcomm)
  rw [ENat.toNat_add (Module.length_ne_top_iff.mpr hf) (Module.length_ne_top_iff.mpr hj'),
    ENat.toNat_add (Module.length_ne_top_iff.mpr hi) (Module.length_ne_top_iff.mpr hg')] at h
  exact_mod_cast h

/-- The order of a product of two nonzero fractions is the sum of their orders. -/
private theorem order_fraction_mul
    {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D] [Ring.KrullDimLE 1 D]
    {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]
    (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero
      (x := Ring.ordFrac D (f * g)) (((mul_ne_zero hf hg).isUnit.map (Ring.ordFrac D)).ne_zero)) =
      Multiplicative.toAdd (WithZero.unzero
        (x := Ring.ordFrac D f) ((hf.isUnit.map (Ring.ordFrac D)).ne_zero)) +
      Multiplicative.toAdd (WithZero.unzero
        (x := Ring.ordFrac D g) ((hg.isUnit.map (Ring.ordFrac D)).ne_zero)) := by
  have h : WithZero.unzero
      (x := Ring.ordFrac D (f * g)) (((mul_ne_zero hf hg).isUnit.map (Ring.ordFrac D)).ne_zero) =
      WithZero.unzero (x := Ring.ordFrac D f) ((hf.isUnit.map (Ring.ordFrac D)).ne_zero) *
        WithZero.unzero (x := Ring.ordFrac D g) ((hg.isUnit.map (Ring.ordFrac D)).ne_zero) := by
    rw [← WithZero.coe_inj]
    simp only [WithZero.coe_unzero, WithZero.coe_mul, map_mul]
  rw [h]
  rfl

/-- If a map induces an injection on the quotients by a compatible pair of submodules, its
colength splits as the colength on the submodules plus the colength on the quotients. -/
private theorem length_coker_eq_add_of_quotient_injective
    {R : Type*} [Ring R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (U : Submodule R M) (V : Submodule R N) (φ : M →ₗ[R] N)
    (hUV : U ≤ V.comap φ) (hbar : Function.Injective (U.mapQ V φ hUV)) :
    Module.length R (N ⧸ LinearMap.range φ) =
      Module.length R (V ⧸ LinearMap.range
        ((φ.domRestrict U).codRestrict V (fun x => hUV x.property))) +
      Module.length R ((N ⧸ V) ⧸ LinearMap.range (U.mapQ V φ hUV)) := by
  let φbar := U.mapQ V φ hUV
  let φU := (φ.domRestrict U).codRestrict V (fun x => hUV x.property)
  have hf : LinearMap.range φU ≤ (LinearMap.range φ).comap V.subtype := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  let f := (LinearMap.range φU).mapQ (LinearMap.range φ) V.subtype hf
  have hg : LinearMap.range φ ≤ (LinearMap.range φbar).comap V.mkQ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨U.mkQ x, rfl⟩
  let g := (LinearMap.range φ).mapQ (LinearMap.range φbar) V.mkQ hg
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φU) z
    change (LinearMap.range φ).mkQ x.1 = 0 at hz
    obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    have hbar0 : φbar (U.mkQ m) = 0 := by
      change V.mkQ (φ m) = 0
      rw [hm]
      exact (Submodule.Quotient.mk_eq_zero _).mpr x.property
    have hmU : m ∈ U := (Submodule.Quotient.mk_eq_zero _).mp
      (hbar (hbar0.trans (map_zero φbar).symm))
    change (LinearMap.range φU).mkQ x = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨⟨m, hmU⟩, Subtype.ext hm⟩
  · intro w
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φbar) w
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective V z
    exact ⟨(LinearMap.range φ).mkQ n, rfl⟩
  · rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro z hz
      obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φ) z
      change (LinearMap.range φbar).mkQ (V.mkQ n) = 0 at hz
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective U z
      have hnm : n - φ m ∈ V := (Submodule.Quotient.eq V).mp hz.symm
      refine ⟨(LinearMap.range φU).mkQ ⟨n - φ m, hnm⟩, ?_⟩
      change (LinearMap.range φ).mkQ (n - φ m) = (LinearMap.range φ).mkQ n
      apply (Submodule.Quotient.eq _).mpr
      exact ⟨-m, by simp⟩
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φU) z
      change (LinearMap.range φbar).mkQ (V.mkQ x.1) = 0
      rw [show V.mkQ x.1 = 0 from (Submodule.Quotient.mk_eq_zero _).mpr x.property, map_zero]

/-- Rescaling the entries of a family by units does not change the submodule they span. -/
private theorem span_units_smul
    {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} (x : ι → M) (a : ι → Rˣ) (s : Set ι) :
    Submodule.span R ((fun i => (a i : R) • x i) '' s) =
      Submodule.span R (x '' s) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change x i ∈ Submodule.span R ((fun i => (a i : R) • x i) '' s)
    have h := (Submodule.span R ((fun i => (a i : R) • x i) '' s)).smul_mem
      (↑(a i)⁻¹ : R) (Submodule.subset_span ⟨i, hi, rfl⟩)
    simpa only [smul_smul, Units.inv_mul, one_smul] using h

/-- Rescaling the entries of an admissible sequence by units leaves it admissible. -/
private theorem admissible_units_smul
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {n : ℕ} (x : Fin n → M)
    (hx : IsAdmissibleSequence (R := R) x) (a : Fin n → Rˣ) :
    IsAdmissibleSequence (R := R) (fun i => (a i : R) • x i) := by
  intro i r hr
  rw [spanBefore, span_units_smul]
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (hx i r hr)

/-- Rescaling the entries of an admissible sequence by units multiplies its symbol by the
product of the residues of those units. -/
private theorem symbol_units_smul
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (e : AdmissibleSequence R M)
    (a : Fin (moduleLength R M) → Rˣ) :
    symbol ⟨fun i => (a i : R) • e.1 i, admissible_units_smul e.1 e.2 a⟩ =
      (∏ i, IsLocalRing.residue R (a i)) • symbol e := by
  classical
  let u (s : Finset (Fin (moduleLength R M))) (i : Fin (moduleLength R M)) : Rˣ :=
    if i ∈ s then a i else 1
  let es (s : Finset (Fin (moduleLength R M))) : AdmissibleSequence R M :=
    ⟨fun i => (u s i : R) • e.1 i, admissible_units_smul e.1 e.2 (u s)⟩
  have h (s : Finset (Fin (moduleLength R M))) :
      symbol (es s) = (∏ i ∈ s, IsLocalRing.residue R (a i)) • symbol e := by
    induction s using Finset.induction with
    | empty =>
      have he : es ∅ = e := by
        apply Subtype.ext
        funext i
        simp [es, u]
      simp [he]
    | @insert i s hi ih =>
      have hupdate : Function.update (es (insert i s)).1 i ((es s).1 i) = (es s).1 := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [es, u, hji]
      have hsym := symbol_eq_residue_smul_of_update (es (insert i s)) (es s) i (a i) 0
        (by simp [es, u, hi]) (zero_mem _) hupdate
      rw [ih, smul_smul] at hsym
      simpa only [Finset.prod_insert hi] using hsym
  have he : es Finset.univ =
      ⟨fun i => (a i : R) • e.1 i, admissible_units_smul e.1 e.2 a⟩ := by
    apply Subtype.ext
    funext i
    simp [es, u]
  simpa only [he] using h Finset.univ

end Module.FiniteLength
