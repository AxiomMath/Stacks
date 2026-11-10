module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GoodSequenceTwoPointSupport
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicDeterminantSymbolScalars
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthColengths
public import StacksFrontier.AlgebraicGeometry.Chow.PrimeFiltrationRestriction

/-!
# The multiplicity of a two-periodic complex and its localized determinant at a prime

Let `(M, φ, ψ)` be a `(2, 1)`-periodic complex of finite modules over a Noetherian local ring
whose cohomology has finite length, and let `q` be a prime with `R / q` of dimension one. Five
sequences with successive quotients `R / q` compute the multiplicity of the complex: one spanning
a submodule of `ker φ`, one spanning a submodule of `ker ψ`, one inside each of those spans
coming from the image of the other differential, and one inside the span of each of the two
concatenations of a kernel sequence with a sequence of lifts. The four colengths they cut out are
the orders of four residues at `q`, and those same residues compare the determinant symbols of
the localized sequences; combining the two readings turns the multiplicity into minus the order
of the periodic determinant of the localized complex.

## Main results

* `AlgebraicGeometry.exact_localizedModule_map_of_isFiniteLength_homology`: at a prime other than
  the closed point the localization of the complex is exact.
* `AlgebraicGeometry.bijective_map_subtype_of_isFiniteLength_quotient` and
  `AlgebraicGeometry.range_map_subtype_eq_ker_map_of_isFiniteLength_quotient`: a submodule of
  finite-length colength fills up the localization, resp. fills up the kernel of the localized
  differential.
* `Module.FiniteLength.subquotEquivMapMkQ` and
  `Module.FiniteLength.primeFiltration_mkQ_of_append`: passing to the quotient by the span of the
  first block of a concatenated sequence preserves its successive quotients, so the colength
  identity coming from `0 → ker φ → M → im φ → 0` applies to the second block.
* `Module.FiniteLength.isFiniteLength_map_mkQ`: the image of a submodule in the quotient by a
  submodule of finite-length colength in it has finite length.
* `Module.FiniteLength.exists_symbol_scalar_localized_span`: the colength of one such span inside
  another is the order of the scalar comparing their localized determinant symbols, read in any
  module identified with the localization of the larger span.
* `AlgebraicGeometry.periodicGamma_symbol_tmul_symbol`: the determinant map of the localized
  complex carries the tensor of two of those symbols to the symbol of their concatenation.
* `AlgebraicGeometry.neg_periodicLength_eq_toAdd_unzero_ordFrac_periodicDeterminant`: the
  multiplicity from the four residues and the determinant comparison they satisfy.
* The five sequences themselves give the same conclusion, in
  `AlgebraicGeometry.neg_periodicLength_eq_toAdd_unzero_ordFrac_periodicDeterminant_of_sequences`.

## Implementation notes

Localization of modules is `LocalizedModule` and of a differential `LocalizedModule.map`; the
localized complex is exact because its cohomology is annihilated by an element outside `q`.
Sequences are presented as in Tags 02QB and 02QC, by the successive subquotients of the spans of
their initial segments, and the localized symbols of two sequences are compared inside the
determinant of the localization of the larger span, transported to the relevant submodule of the
localization of `M` by `AlgebraicGeometry.localizedSubtypeEquivRange` or, when the span already
fills up the localization, by `LinearEquiv.ofBijective`. The two concatenations are handed over
as named sequences `wφ` and `wψ` together with their defining equations, which lets the second
one be indexed by `Fin (b + a)` like the first. The two colength identities `m_φ = k_φ + i_φ` and
`m_ψ = k_ψ + i_ψ` of the source are derived rather than assumed: the filtration of a
concatenation descends to the quotient by the span of its first block, which is what
`Module.FiniteLength.length_quotient_eq_ker_add_range_of_isFiniteLength_map_mkQ` consumes.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/
@[expose] public section

universe u v

namespace Module.FiniteLength

/-- A function applied to a concatenation of two sequences is the concatenation of the two
images. -/
private theorem comp_fin_append {A : Type u} {B : Type v} {n m : ℕ} (g : A → B)
    (u : Fin n → A) (c : Fin m → A) (k : Fin (n + m)) :
    g (Fin.append u c k) = Fin.append (fun i ↦ g (u i)) (fun i ↦ g (c i)) k := by
  refine Fin.addCases (motive := fun k ↦ g (Fin.append u c k) =
    Fin.append (fun i ↦ g (u i)) (fun i ↦ g (c i)) k) (fun i ↦ ?_) (fun i ↦ ?_) k <;> simp

/-- Reindexing the two blocks of a concatenation along equalities of their lengths reindexes the
concatenation. -/
private theorem fin_append_cast {A : Type u} {n m n' m' Nn : ℕ}
    (hn : n' = n) (hm : m' = m) (h₁ : Nn = n' + m') (h₂ : Nn = n + m)
    (u : Fin n → A) (c : Fin m → A) (j : Fin Nn) :
    Fin.append (fun i : Fin n' ↦ u (Fin.cast hn i)) (fun i : Fin m' ↦ c (Fin.cast hm i))
        (Fin.cast h₁ j) = Fin.append u c (Fin.cast h₂ j) := by
  subst hn
  subst hm
  subst h₁
  simp

/-- An admissible sequence of a module is determined by the images of its terms under an
injective map. -/
theorem admissibleSequence_ext {R : Type u} {A B : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (ι : A →ₗ[R] B)
    (hι : Function.Injective ι) {as bs : AdmissibleSequence R A}
    (h : ∀ i, ι (as.1 i) = ι (bs.1 i)) : as = bs :=
  Subtype.ext (funext fun i ↦ hι (h i))

/-- Transporting a generating admissible sequence along an isomorphism of modules keeps it
generating. -/
theorem span_range_admissibleSequenceMap_eq_top {R : Type u} {A B : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (E : A ≃ₗ[R] B) (hlen : moduleLength R A = moduleLength R B) (e : AdmissibleSequence R A)
    (he : Submodule.span R (Set.range e.1) = ⊤) :
    Submodule.span R (Set.range (admissibleSequenceMap E hlen e).1) = ⊤ := by
  have hrange : Set.range (admissibleSequenceMap E hlen e).1 =
      (E : A →ₗ[R] B) '' Set.range e.1 := by
    ext c
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.1 (Fin.cast hlen.symm j), Set.mem_range_self _, rfl⟩
    · rintro ⟨d, ⟨i, rfl⟩, rfl⟩
      refine ⟨Fin.cast hlen i, ?_⟩
      change E (e.1 (Fin.cast hlen.symm (Fin.cast hlen i))) = E (e.1 i)
      rw [show Fin.cast hlen.symm (Fin.cast hlen i) = i from Fin.ext rfl]
  rw [hrange, ← Submodule.map_span, he, Submodule.map_top, LinearMap.range_eq_top]
  exact E.surjective

/-- Transporting a proportionality of symbols along an isomorphism of modules. -/
theorem symbol_admissibleSequenceMap_smul {R : Type u} {A B : Type v}
    [CommRing R] [IsLocalRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (E : A ≃ₗ[R] B) (hlen : moduleLength R A = moduleLength R B)
    (e₁ e₂ : AdmissibleSequence R A) (f : IsLocalRing.ResidueField R)
    (hf : symbol e₁ = f • symbol e₂) :
    symbol (admissibleSequenceMap E hlen e₁) =
      f • symbol (admissibleSequenceMap E hlen e₂) := by
  rw [← determinantEquiv_symbol E hlen, ← determinantEquiv_symbol E hlen, hf, map_smul]

/-- For `W ≤ B ≤ A`, passing to the quotient by `W` identifies the subquotient of `A` by `B`
with the subquotient cut out by their images, presented as any pair of submodules equal to
them. -/
noncomputable def subquotEquivMapMkQ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] (W : Submodule R M) {A B : Submodule R M} (hWB : W ≤ B)
    {A₂ B₂ : Submodule R (M ⧸ W)} (hA : A.map W.mkQ = A₂) (hB : B.map W.mkQ = B₂) :
    (↥A ⧸ B.submoduleOf A) ≃ₗ[R] (↥A₂ ⧸ B₂.submoduleOf A₂) := by
  subst hA
  subst hB
  have hmemA : ∀ c ∈ A, W.mkQ c ∈ A.map W.mkQ := fun c hc ↦ Submodule.mem_map_of_mem hc
  have hmemB : ∀ c : M, W.mkQ c ∈ Submodule.map W.mkQ B ↔ c ∈ B := by
    intro c
    rw [← Submodule.mem_comap (f := W.mkQ) (p := Submodule.map W.mkQ B),
      Submodule.comap_map_mkQ]
    exact ⟨fun hc ↦ (sup_le hWB le_rfl) hc, fun hc ↦ (le_sup_right : B ≤ W ⊔ B) hc⟩
  have hpsurj : Function.Surjective (W.mkQ.restrict hmemA) := by
    rintro ⟨v, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have hker : B.submoduleOf A =
      LinearMap.ker (((Submodule.map W.mkQ B).submoduleOf (A.map W.mkQ)).mkQ ∘ₗ
        W.mkQ.restrict hmemA) := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    change (c : M) ∈ B ↔ W.mkQ (c : M) ∈ Submodule.map W.mkQ B
    exact (hmemB (c : M)).symm
  exact (Submodule.quotEquivOfEq _ _ hker).trans
    (LinearMap.quotKerEquivOfSurjective _ ((Submodule.mkQ_surjective _).comp hpsurj))

/-- The span of the entries of a concatenation preceding an index in the second block is the span
of the whole first block together with the span of the preceding entries of the second. -/
public theorem spanBefore_append_natAdd {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {n m : ℕ} (u : Fin n → M) (c : Fin m → M) (i : Fin m) :
    spanBefore (R := R) (Fin.append u c) (Fin.natAdd n i) =
      Submodule.span R (Set.range u) ⊔ spanBefore (R := R) c i := by
  have himg : Fin.append u c '' Set.Iio (Fin.natAdd n i) =
      Set.range u ∪ c '' Set.Iio i := by
    ext w
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine Fin.addCases (motive := fun k ↦ k ∈ Set.Iio (Fin.natAdd n i) →
        Fin.append u c k ∈ Set.range u ∪ c '' Set.Iio i) (fun k' _ ↦ ?_) (fun k' hk' ↦ ?_) k hk
      · exact Or.inl ⟨k', by simp⟩
      · exact Or.inr ⟨k', (Fin.natAdd_lt_natAdd_iff n).mp hk', by simp⟩
    · rintro (⟨k', rfl⟩ | ⟨k', hk', rfl⟩)
      · refine ⟨Fin.castAdd m k', ?_, by simp⟩
        exact Fin.lt_def.mpr (by simpa using Nat.lt_of_lt_of_le k'.isLt (Nat.le_add_right n i.val))
      · exact ⟨Fin.natAdd n k', (Fin.natAdd_lt_natAdd_iff n).mpr hk', by simp⟩
  rw [spanBefore, himg, Submodule.span_union, spanBefore]

/-- The successive quotients of a concatenated sequence descend to the quotient by the span of
its first block: if the concatenation has successive quotients `R / q`, so does the image of its
second block. -/
theorem primeFiltration_mkQ_of_append {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {n m Nn : ℕ} (hNn : Nn = n + m) (q : Ideal R)
    (u : Fin n → M) (c : Fin m → M) (w : Fin Nn → M)
    (hw : ∀ j, w j = Fin.append u c (Fin.cast hNn j))
    (hwf : ∀ j : Fin Nn,
      Nonempty
        (((spanBefore (R := R) w j ⊔ R ∙ w j : Submodule R M) ⧸
            (spanBefore (R := R) w j).comap
              (spanBefore (R := R) w j ⊔ R ∙ w j : Submodule R M).subtype) ≃ₗ[R] R ⧸ q)) :
    ∀ i : Fin m,
      Nonempty
        (((spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i ⊔
              R ∙ (Submodule.span R (Set.range u)).mkQ (c i) :
            Submodule R (M ⧸ Submodule.span R (Set.range u))) ⧸
            (spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i).comap
              (spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i ⊔
                R ∙ (Submodule.span R (Set.range u)).mkQ (c i) :
              Submodule R (M ⧸ Submodule.span R (Set.range u))).subtype) ≃ₗ[R] R ⧸ q) := by
  intro i
  have hwfun : w = fun k : Fin Nn ↦ Fin.append u c (Fin.cast hNn k) := funext hw
  have hcastj : Fin.cast hNn (Fin.cast hNn.symm (Fin.natAdd n i)) = Fin.natAdd n i := Fin.ext rfl
  have hsb : spanBefore (R := R) w (Fin.cast hNn.symm (Fin.natAdd n i)) =
      Submodule.span R (Set.range u) ⊔ spanBefore (R := R) c i := by
    rw [hwfun, spanBefore_cast hNn (Fin.append u c), hcastj, spanBefore_append_natAdd]
  have hwj : w (Fin.cast hNn.symm (Fin.natAdd n i)) = c i := by
    rw [hw, hcastj, Fin.append_right]
  have hWbot : (Submodule.span R (Set.range u)).map
      (Submodule.span R (Set.range u)).mkQ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro v ⟨d, hd, rfl⟩
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hd
  have hBdown : spanBefore (R := R)
      (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i =
      (spanBefore (R := R) c i).map (Submodule.span R (Set.range u)).mkQ :=
    spanBefore_comp c (Submodule.span R (Set.range u)).mkQ i
  have hB : (spanBefore (R := R) w (Fin.cast hNn.symm (Fin.natAdd n i))).map
      (Submodule.span R (Set.range u)).mkQ =
      spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i := by
    rw [hsb, Submodule.map_sup, hWbot, bot_sup_eq, hBdown]
  have hA : (spanBefore (R := R) w (Fin.cast hNn.symm (Fin.natAdd n i)) ⊔
        R ∙ w (Fin.cast hNn.symm (Fin.natAdd n i))).map
      (Submodule.span R (Set.range u)).mkQ =
      (spanBefore (R := R) (fun k ↦ (Submodule.span R (Set.range u)).mkQ (c k)) i ⊔
        R ∙ (Submodule.span R (Set.range u)).mkQ (c i)) := by
    rw [Submodule.map_sup, hB, hwj, Submodule.map_span, Set.image_singleton]
  exact ⟨(subquotEquivMapMkQ (Submodule.span R (Set.range u))
    (hsb ▸ le_sup_left) hA hB).symm.trans
      (hwf (Fin.cast hNn.symm (Fin.natAdd n i))).some⟩

/-- If a submodule has finite-length colength in a larger one, the image of the larger one in the
quotient by the smaller has finite length. -/
theorem isFiniteLength_map_mkQ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M]
    [Module R M] {W K : Submodule R M}
    (h : IsFiniteLength R (↥K ⧸ W.submoduleOf K)) :
    IsFiniteLength R ↥(K.map W.mkQ) := by
  have hmem : ∀ c ∈ K, W.mkQ c ∈ K.map W.mkQ := fun c hc ↦ Submodule.mem_map_of_mem hc
  have hle : W.submoduleOf K ≤ LinearMap.ker (W.mkQ.restrict hmem) := by
    intro c hc
    rw [LinearMap.mem_ker]
    refine Subtype.ext ?_
    change W.mkQ (c : M) = (0 : M ⧸ W)
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hc
  refine h.of_surjective (f := Submodule.liftQ _ (W.mkQ.restrict hmem) hle) ?_
  rintro ⟨v, c, hc, rfl⟩
  exact ⟨Submodule.Quotient.mk ⟨c, hc⟩, rfl⟩

/-- Mapping the span of a concatenation, whose first block is killed by `f`, gives the span of the
images of the second block. -/
private theorem map_span_range_of_append {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {n m Nn : ℕ}
    (hNn : Nn = n + m) (u : Fin n → M) (c : Fin m → M) (w : Fin Nn → M)
    (hw : ∀ j, w j = Fin.append u c (Fin.cast hNn j)) (hu : ∀ i, f (u i) = 0) :
    (Submodule.span R (Set.range w)).map f = Submodule.span R (Set.range fun i ↦ f (c i)) := by
  rw [Submodule.map_span]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨d, ⟨j, rfl⟩, rfl⟩
    rw [hw j]
    refine Fin.addCases (motive := fun k ↦
      f (Fin.append u c k) ∈ Submodule.span R (Set.range fun i ↦ f (c i)))
      (fun i ↦ ?_) (fun i ↦ ?_) (Fin.cast hNn j)
    · rw [Fin.append_left, hu]
      exact Submodule.zero_mem _
    · rw [Fin.append_right]
      exact Submodule.subset_span ⟨i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨w (Fin.cast hNn.symm (Fin.natAdd n i)), ⟨_, rfl⟩, ?_⟩
    rw [hw, show Fin.cast hNn (Fin.cast hNn.symm (Fin.natAdd n i)) = Fin.natAdd n i from
      Fin.ext rfl, Fin.append_right]

/-- For two sequences of the same number of terms with successive quotients `R / q`, the second
generating a submodule `P` whose span contains the span of the first, the localized symbols of
the two sequences — read inside any module identified with the localization of `P` — are
proportional, with the order of the comparison scalar the colength of the smaller span. -/
theorem exists_symbol_scalar_localized_span
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] [Ring.KrullDimLE 1 (R ⧸ q)]
    (hdim : ringKrullDim (R ⧸ q) = 1)
    {n : ℕ} (v w : Fin n → M)
    (hvf : ∀ i : Fin n,
      Nonempty
        (((spanBefore (R := R) v i ⊔ R ∙ v i : Submodule R M) ⧸
            (spanBefore (R := R) v i).comap
              (spanBefore (R := R) v i ⊔ R ∙ v i : Submodule R M).subtype) ≃ₗ[R] R ⧸ q))
    (hwf : ∀ i : Fin n,
      Nonempty
        (((spanBefore (R := R) w i ⊔ R ∙ w i : Submodule R M) ⧸
            (spanBefore (R := R) w i).comap
              (spanBefore (R := R) w i ⊔ R ∙ w i : Submodule R M).subtype) ≃ₗ[R] R ⧸ q))
    (hvw : Submodule.span R (Set.range v) ≤ Submodule.span R (Set.range w))
    {N : Type max v u} [AddCommGroup N] [Module (Localization.AtPrime q) N]
    (ι : N →ₗ[Localization.AtPrime q] LocalizedModule q.primeCompl M)
    (E : LocalizedModule q.primeCompl ↥(Submodule.span R (Set.range w)) ≃ₗ[Localization.AtPrime q]
      N)
    (hE : ∀ c, ι (E c) =
      LocalizedModule.map q.primeCompl (Submodule.span R (Set.range w)).subtype c) :
    ∃ hlen : moduleLength (Localization.AtPrime q) N = n,
      ∃ vs ws : AdmissibleSequence (Localization.AtPrime q) N,
        (∀ i, ι (vs.1 i) = LocalizedModule.mk (v (Fin.cast hlen i)) 1) ∧
          (∀ i, ι (ws.1 i) = LocalizedModule.mk (w (Fin.cast hlen i)) 1) ∧
          Submodule.span (Localization.AtPrime q) (Set.range ws.1) = ⊤ ∧
          ∃ f : q.ResidueField, ∃ hf : f ≠ 0, symbol vs = f • symbol ws ∧
            ((Module.length R (↥(Submodule.span R (Set.range w)) ⧸
                (Submodule.span R (Set.range v)).submoduleOf
                  (Submodule.span R (Set.range w)))).toNat : ℤ) =
              Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) f)
                ((hf.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero) ) := by
  have hNoeth : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  have hvP : ∀ i, v i ∈ Submodule.span R (Set.range v) := fun i ↦
    Submodule.subset_span ⟨i, rfl⟩
  have hwP : ∀ i, w i ∈ Submodule.span R (Set.range w) := fun i ↦
    Submodule.subset_span ⟨i, rfl⟩
  have hvVspan : Submodule.span R
      (Set.range (fun i ↦ (⟨v i, hvP i⟩ : ↥(Submodule.span R (Set.range v))))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _ hvP).mpr rfl
  have hwPspan : Submodule.span R
      (Set.range (fun i ↦ (⟨w i, hwP i⟩ : ↥(Submodule.span R (Set.range w))))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff _ hwP).mpr rfl
  obtain ⟨hlenP, hadmv, hadmw, f, hf, hsym, hcol⟩ :=
    exists_symbol_scalar_length_quotient_range_eq_order q hdim n
      (fun i ↦ (⟨v i, hvP i⟩ : ↥(Submodule.span R (Set.range v))))
      (fun i ↦ (⟨w i, hwP i⟩ : ↥(Submodule.span R (Set.range w))))
      hvVspan (primeFiltration_restrict _ q v hvP hvf) hwPspan
      (primeFiltration_restrict _ q w hwP hwf)
      (Submodule.inclusion hvw) (Submodule.inclusion_injective hvw)
  have hlenE : moduleLength (Localization.AtPrime q)
      (LocalizedModule q.primeCompl ↥(Submodule.span R (Set.range w))) =
      moduleLength (Localization.AtPrime q) N :=
    moduleLength_eq_of_equiv E
  have hcast : ∀ i : Fin (moduleLength (Localization.AtPrime q) N),
      Fin.cast hlenP (Fin.cast hlenE.symm i) = Fin.cast (hlenE.symm.trans hlenP) i :=
    fun _ ↦ Fin.ext rfl
  set Av : AdmissibleSequence (Localization.AtPrime q)
      (LocalizedModule q.primeCompl ↥(Submodule.span R (Set.range w))) :=
    ⟨_, hadmv⟩ with hAv
  set Aw : AdmissibleSequence (Localization.AtPrime q)
      (LocalizedModule q.primeCompl ↥(Submodule.span R (Set.range w))) :=
    ⟨_, hadmw⟩ with hAw
  have hAwspan : Submodule.span (Localization.AtPrime q) (Set.range Aw.1) = ⊤ :=
    span_localized_mk_cast_eq_top hlenP q.primeCompl
      (fun i ↦ (⟨w i, hwP i⟩ : ↥(Submodule.span R (Set.range w)))) hwPspan
  refine ⟨hlenE.symm.trans hlenP, admissibleSequenceMap E hlenE Av,
    admissibleSequenceMap E hlenE Aw, fun i ↦ ?_, fun i ↦ ?_,
    span_range_admissibleSequenceMap_eq_top E hlenE Aw hAwspan, f, hf,
    symbol_admissibleSequenceMap_smul E hlenE Av Aw f hsym, ?_⟩
  · change ι (E (LocalizedModule.mk _ 1)) = _
    rw [hE, LocalizedModule.map_mk, hcast i]
    rfl
  · change ι (E (LocalizedModule.mk _ 1)) = _
    rw [hE, LocalizedModule.map_mk, hcast i]
    rfl
  · have hr : LinearMap.range (Submodule.inclusion hvw) =
        (Submodule.span R (Set.range v)).submoduleOf (Submodule.span R (Set.range w)) :=
      Submodule.range_inclusion _ _ hvw
    rw [← hr]
    exact hcol

end Module.FiniteLength

namespace AlgebraicGeometry

open Module.FiniteLength

/-- If a localized differential kills `m / s`, then a multiple of `m` by an element outside the
prime lies in `X` once `d` kills the colength of `X` in the kernel. -/
private theorem exists_smul_mem_of_map_mk_eq_zero {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (φ : Module.End R M) (q : Ideal R) [q.IsPrime] {X : Submodule R M}
    {d : R}
    (hd : ∀ x : ↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ), d • x = 0)
    (m : M) (s : q.primeCompl)
    (hz : LocalizedModule.map q.primeCompl φ (LocalizedModule.mk m s) = 0) :
    ∃ u : q.primeCompl, d • (u : R) • m ∈ X := by
  rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk (1 : q.primeCompl),
    LocalizedModule.mk_eq] at hz
  obtain ⟨u, hu⟩ := hz
  simp only [one_smul, smul_zero, Submonoid.smul_def] at hu
  have hmem : (u : R) • m ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_smul, ← Submonoid.smul_def, Submonoid.smul_def]
    exact hu
  have hquot := hd (Submodule.Quotient.mk (⟨(u : R) • m, hmem⟩ : ↥(LinearMap.ker φ)))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hquot
  exact ⟨u, hquot⟩

/-- At a prime other than the closed point, a two-periodic complex over a Noetherian local ring
whose cohomology at that spot has finite length becomes exact after localizing: the cohomology
is annihilated by an element outside the prime. -/
theorem exact_localizedModule_map_of_isFiniteLength_homology
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0)
    (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R)
    (hH : IsFiniteLength R
      (↥(LinearMap.ker φ) ⧸ (LinearMap.range ψ).submoduleOf (LinearMap.ker φ))) :
    Function.Exact (LocalizedModule.map q.primeCompl ψ)
      (LocalizedModule.map q.primeCompl φ) := by
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  obtain ⟨d, hdq, hd⟩ := exists_notMem_smul_eq_zero_of_isFiniteLength hH q hq
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro z hz
    induction z using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨u, n, hn⟩ := exists_smul_mem_of_map_mk_eq_zero φ q hd m s (LinearMap.mem_ker.mp hz)
      refine ⟨LocalizedModule.mk n (⟨d, hdq⟩ * (u * s)), ?_⟩
      rw [LocalizedModule.map_mk, hn]
      rw [show d • (u : R) • m = (⟨d, hdq⟩ : q.primeCompl) • ((u : R) • m) from rfl,
        LocalizedModule.mk_cancel_common_left,
        show (u : R) • m = (u : q.primeCompl) • m from rfl,
        LocalizedModule.mk_cancel_common_left]
  · rintro z ⟨w, rfl⟩
    induction w using LocalizedModule.induction_on with
    | h m s =>
      rw [LinearMap.mem_ker, LocalizedModule.map_mk, LocalizedModule.map_mk,
        show φ (ψ m) = 0 from LinearMap.congr_fun hφψ m, LocalizedModule.zero_mk]

/-- A submodule whose quotient has finite length becomes everything after localizing at a prime
other than the closed point. -/
theorem bijective_map_subtype_of_isFiniteLength_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R) (P : Submodule R M)
    (hP : IsFiniteLength R (M ⧸ P)) :
    Function.Bijective (LocalizedModule.map q.primeCompl P.subtype) := by
  obtain ⟨d, hdq, hd⟩ := exists_notMem_smul_eq_zero_of_isFiniteLength hP q hq
  refine ⟨LocalizedModule.map_injective _ _ P.subtype_injective, fun w ↦ ?_⟩
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have hmem : d • m ∈ P := by
      have h := hd (Submodule.Quotient.mk m)
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    refine ⟨LocalizedModule.mk ⟨d • m, hmem⟩ (⟨d, hdq⟩ * s), ?_⟩
    rw [LocalizedModule.map_mk]
    exact LocalizedModule.mk_cancel_common_left ⟨d, hdq⟩ s m

/-- If a submodule of the kernel of an endomorphism has finite-length colength in that kernel,
then after localizing at a prime other than the closed point it fills up the kernel of the
localized endomorphism. -/
theorem range_map_subtype_eq_ker_map_of_isFiniteLength_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ : Module.End R M)
    (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R)
    {X : Submodule R M} (hXK : X ≤ LinearMap.ker φ)
    (hfin : IsFiniteLength R (↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ))) :
    LinearMap.range (LocalizedModule.map q.primeCompl X.subtype) =
      LinearMap.ker (LocalizedModule.map q.primeCompl φ) := by
  have : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  obtain ⟨d, hdq, hd⟩ := exists_notMem_smul_eq_zero_of_isFiniteLength hfin q hq
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    induction v using LocalizedModule.induction_on with
    | h m s =>
      rw [LinearMap.mem_ker, LocalizedModule.map_mk, LocalizedModule.map_mk,
        show φ (X.subtype m) = 0 from hXK m.2, LocalizedModule.zero_mk]
  · intro w hw
    induction w using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨u, hX⟩ := exists_smul_mem_of_map_mk_eq_zero φ q hd m s (LinearMap.mem_ker.mp hw)
      refine ⟨LocalizedModule.mk ⟨d • (u : R) • m, hX⟩ (⟨d, hdq⟩ * (u * s)), ?_⟩
      rw [LocalizedModule.map_mk]
      rw [show X.subtype ⟨d • (u : R) • m, hX⟩ =
          (⟨d, hdq⟩ : q.primeCompl) • ((u : R) • m) from rfl,
        LocalizedModule.mk_cancel_common_left,
        show (u : R) • m = (u : q.primeCompl) • m from rfl,
        LocalizedModule.mk_cancel_common_left]

/-- The determinant map of the two short exact sequences cut out by the images of an exact
localized two-periodic complex carries the tensor of the symbols of two localized sequences to
the symbol of their concatenation: if the first spans the image of `ψ` after localizing and the
second is the image under `φ` of a sequence of lifts, the concatenation of the first with those
lifts is the sequence whose symbol comes out. -/
theorem periodicGamma_symbol_tmul_symbol
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (φ ψ : Module.End R M) (q : Ideal R) [q.IsPrime]
    (hMq : IsFiniteLength (Localization.AtPrime q) (LocalizedModule q.primeCompl M))
    (hex2 : Function.Exact (LocalizedModule.map q.primeCompl ψ)
      (LocalizedModule.map q.primeCompl φ))
    {n m Nn : ℕ} (hNn : Nn = n + m) (u : Fin n → M) (c : Fin m → M)
    (us : AdmissibleSequence (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl ψ)))
    (vs : AdmissibleSequence (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl φ)))
    (ws : AdmissibleSequence (Localization.AtPrime q) (LocalizedModule q.primeCompl M))
    (hlenU : moduleLength (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl ψ)) = n)
    (hlenV : moduleLength (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl φ)) = m)
    (hlenW : moduleLength (Localization.AtPrime q) (LocalizedModule q.primeCompl M) = Nn)
    (hus : ∀ i, (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype (us.1 i) =
      LocalizedModule.mk (u (Fin.cast hlenU i)) 1)
    (hvs : ∀ i, (LinearMap.range (LocalizedModule.map q.primeCompl φ)).subtype (vs.1 i) =
      LocalizedModule.mk (φ (c (Fin.cast hlenV i))) 1)
    (hws : ∀ j, ws.1 j =
      LocalizedModule.mk (Fin.append u c (Fin.cast (hlenW.trans hNn) j)) 1)
    (hus0 : symbol us ≠ 0) (hvs0 : symbol vs ≠ 0) :
    periodicGamma (LocalizedModule.map q.primeCompl φ) (LocalizedModule.map q.primeCompl ψ)
        hex2 hMq (symbol us ⊗ₜ[q.ResidueField] symbol vs) = symbol ws := by
  have hsurj : Function.Surjective
      (LocalizedModule.map q.primeCompl φ).rangeRestrict :=
    LinearMap.surjective_rangeRestrict _
  have hinj : Function.Injective
      (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype :=
    Submodule.injective_subtype _
  have hexact : Function.Exact
      (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype
      (LocalizedModule.map q.primeCompl φ).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    exact hex2.linearMap_ker_eq
  have hK : IsFiniteLength (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl ψ)) := hMq.of_injective hinj
  have hQ : IsFiniteLength (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl φ)) :=
    hMq.of_injective (Submodule.injective_subtype _)
  have hlifts : ∀ i, (LocalizedModule.map q.primeCompl φ).rangeRestrict
      (LocalizedModule.mk (c (Fin.cast hlenV i)) 1) = vs.1 i := by
    intro i
    refine Subtype.ext ?_
    change (LocalizedModule.map q.primeCompl φ)
        (LocalizedModule.mk (c (Fin.cast hlenV i)) 1) =
      (LinearMap.range (LocalizedModule.map q.primeCompl φ)).subtype (vs.1 i)
    rw [LocalizedModule.map_mk, hvs i]
  obtain ⟨hlength, hadm, heq⟩ :=
    determinantExactSequenceMap_spec
      (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype
      (LocalizedModule.map q.primeCompl φ).rangeRestrict hinj hsurj hexact hK hMq hQ
      us vs hus0 hvs0 (fun i ↦ LocalizedModule.mk (c (Fin.cast hlenV i)) 1) hlifts
  refine heq.trans (congrArg symbol (Subtype.ext (funext fun j ↦ ?_)))
  change Fin.append
      (fun i ↦ (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype (us.1 i))
      (fun i ↦ LocalizedModule.mk (c (Fin.cast hlenV i)) (1 : q.primeCompl))
      (Fin.cast hlength j) = ws.1 j
  calc Fin.append
        (fun i ↦ (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype (us.1 i))
        (fun i ↦ LocalizedModule.mk (c (Fin.cast hlenV i)) (1 : q.primeCompl))
        (Fin.cast hlength j)
      = Fin.append
          (fun i ↦ LocalizedModule.mk (u (Fin.cast hlenU i)) (1 : q.primeCompl))
          (fun i ↦ LocalizedModule.mk (c (Fin.cast hlenV i)) (1 : q.primeCompl))
          (Fin.cast hlength j) := by
        congr 1
        exact funext hus
    _ = Fin.append (fun i ↦ LocalizedModule.mk (u i) (1 : q.primeCompl))
          (fun i ↦ LocalizedModule.mk (c i) (1 : q.primeCompl))
          (Fin.cast (hlenW.trans hNn) j) :=
        fin_append_cast hlenU hlenV hlength (hlenW.trans hNn)
          (fun i ↦ LocalizedModule.mk (u i) (1 : q.primeCompl))
          (fun i ↦ LocalizedModule.mk (c i) (1 : q.primeCompl)) j
    _ = LocalizedModule.mk (Fin.append u c (Fin.cast (hlenW.trans hNn) j))
          (1 : q.primeCompl) :=
        (comp_fin_append (fun a ↦ LocalizedModule.mk a (1 : q.primeCompl)) u c _).symm
    _ = ws.1 j := (hws j).symm

/-- Replacing a nonzero fraction by an equal one does not change its order. -/
private theorem toAdd_unzero_ordFrac_congr {D : Type u} [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [Ring.KrullDimLE 1 D] {K : Type v} [Field K] [Algebra D K]
    [IsFractionRing D K] (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f = g) :
    Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D f)
        ((hf.isUnit.map (Ring.ordFrac D)).ne_zero)) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac D g)
        ((hg.isUnit.map (Ring.ordFrac D)).ne_zero)) := by
  subst hfg
  rfl

/-- **The five-sequence computation of the multiplicity.** For a `(2, 1)`-periodic complex over a
Noetherian local ring and a prime `q` with `R / q` of dimension at most one, suppose the four
colengths attached to five good sequences are the orders of residues `g`, `h`, `f_φ`, `f_ψ` at
`q`, and that those residues compare the determinant symbols of the localized sequences as in
the source. Then the multiplicity of the complex is minus the order of the periodic determinant
of its localization at `q`. -/
theorem neg_periodicLength_eq_toAdd_unzero_ordFrac_periodicDeterminant
    {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v}
    [AddCommGroup M] [Module R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (q : Ideal R) [q.IsPrime] [Ring.KrullDimLE 1 (R ⧸ q)]
    (hMq : IsFiniteLength (Localization.AtPrime q) (LocalizedModule q.primeCompl M))
    (hex1 : Function.Exact (LocalizedModule.map q.primeCompl φ)
      (LocalizedModule.map q.primeCompl ψ))
    (hex2 : Function.Exact (LocalizedModule.map q.primeCompl ψ)
      (LocalizedModule.map q.primeCompl φ))
    {X S T Y Vφ Vψ Z : Submodule R M}
    (hSX : S ≤ X) (hXK : X ≤ LinearMap.ker φ) (hSI : S ≤ LinearMap.range ψ)
    (hYT : Y ≤ T) (hTK : T ≤ LinearMap.ker ψ) (hYI : Y ≤ LinearMap.range φ)
    (hZφ : Z ≤ Vφ) (hZψ : Z ≤ Vψ)
    (hmφ : Module.length R (M ⧸ Vφ) =
      Module.length R (↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ)) +
        Module.length R (↥(LinearMap.range φ) ⧸ Y.submoduleOf (LinearMap.range φ)))
    (hmψ : Module.length R (M ⧸ Vψ) =
      Module.length R (↥(LinearMap.ker ψ) ⧸ T.submoduleOf (LinearMap.ker ψ)) +
        Module.length R (↥(LinearMap.range ψ) ⧸ S.submoduleOf (LinearMap.range ψ)))
    (hfinφ : Module.length R (↥(LinearMap.ker φ) ⧸ S.submoduleOf (LinearMap.ker φ)) ≠ ⊤)
    (hfinψ : Module.length R (↥(LinearMap.ker ψ) ⧸ Y.submoduleOf (LinearMap.ker ψ)) ≠ ⊤)
    (hfinZ : Module.length R (M ⧸ Z) ≠ ⊤)
    (xs ss : AdmissibleSequence (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl ψ)))
    (ts ys : AdmissibleSequence (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl φ)))
    (hxs : Submodule.span (Localization.AtPrime q) (Set.range xs.1) = ⊤)
    (hts : Submodule.span (Localization.AtPrime q) (Set.range ts.1) = ⊤)
    (g h fφ fψ : q.ResidueField) (hg : g ≠ 0) (hh : h ≠ 0) (hfφ : fφ ≠ 0) (hfψ : fψ ≠ 0)
    (hys : symbol ys = h • symbol ts) (hss : symbol ss = g • symbol xs)
    (hzz : fφ • periodicGamma (LocalizedModule.map q.primeCompl φ)
          (LocalizedModule.map q.primeCompl ψ) hex2 hMq
          (symbol xs ⊗ₜ[q.ResidueField] symbol ys) =
        fψ • periodicGamma (LocalizedModule.map q.primeCompl ψ)
          (LocalizedModule.map q.primeCompl φ) hex1 hMq
          (symbol ts ⊗ₜ[q.ResidueField] symbol ss))
    (hgX : ((Module.length R (↥X ⧸ S.submoduleOf X)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) g)
        ((hg.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero)))
    (hhT : ((Module.length R (↥T ⧸ Y.submoduleOf T)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) h)
        ((hh.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero)))
    (hδφ : ((Module.length R (↥Vφ ⧸ Z.submoduleOf Vφ)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) fφ)
        ((hfφ.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero)))
    (hδψ : ((Module.length R (↥Vψ ⧸ Z.submoduleOf Vψ)).toNat : ℤ) =
      Multiplicative.toAdd (WithZero.unzero (x := Ring.ordFrac (R ⧸ q) fψ)
        ((hfψ.isUnit.map (Ring.ordFrac (R ⧸ q))).ne_zero))) :
    -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      Multiplicative.toAdd (WithZero.unzero
        (x := Ring.ordFrac (R ⧸ q)
          ((periodicDeterminant (LocalizedModule.map q.primeCompl φ)
            (LocalizedModule.map q.primeCompl ψ) hex1 hex2 hMq : q.ResidueField)))
        (((periodicDeterminant (LocalizedModule.map q.primeCompl φ)
            (LocalizedModule.map q.primeCompl ψ) hex1 hex2 hMq).isUnit.map
          (Ring.ordFrac (R ⧸ q))).ne_zero)) := by
  set dd : q.ResidueField :=
    (periodicDeterminant (LocalizedModule.map q.primeCompl φ)
      (LocalizedModule.map q.primeCompl ψ) hex1 hex2 hMq : q.ResidueField) with hdd
  have hdd0 : dd ≠ 0 := (periodicDeterminant _ _ hex1 hex2 hMq).ne_zero
  set k : ℕ :=
    moduleLength (Localization.AtPrime q)
        ↥(LinearMap.range (LocalizedModule.map q.primeCompl φ)) *
      moduleLength (Localization.AtPrime q)
        ↥(LinearMap.range (LocalizedModule.map q.primeCompl ψ)) with hk
  have hstep := periodicDeterminant_mul_eq_mul_of_symbol_smul
    (LocalizedModule.map q.primeCompl φ) (LocalizedModule.map q.primeCompl ψ) hex1 hex2 hMq
    xs ss ts ys hxs hts g h fφ fψ hys hss hzz
  have hsq : ((-1 : q.ResidueField) ^ k) * ((-1 : q.ResidueField) ^ k) = 1 := by
    rw [← mul_pow]; norm_num
  have hne : ((-1 : q.ResidueField) ^ k) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hkey : dd * (fψ * g) = ((-1 : q.ResidueField) ^ k) * (fφ * h) := by
    rw [hstep]
    calc dd * (fψ * g)
        = (((-1 : q.ResidueField) ^ k * (-1 : q.ResidueField) ^ k) * dd) * (fψ * g) := by
          rw [hsq, one_mul]
      _ = (-1 : q.ResidueField) ^ k * (((-1 : q.ResidueField) ^ k * dd) * (fψ * g)) := by ring
  have hcong := toAdd_unzero_ordFrac_congr (D := R ⧸ q) (dd * (fψ * g))
    ((-1 : q.ResidueField) ^ k * (fφ * h)) (mul_ne_zero hdd0 (mul_ne_zero hfψ hg))
    (mul_ne_zero hne (mul_ne_zero hfφ hh)) hkey
  rw [toAdd_unzero_ordFrac_mul (D := R ⧸ q) dd (fψ * g) hdd0 (mul_ne_zero hfψ hg),
    toAdd_unzero_ordFrac_mul (D := R ⧸ q) fψ g hfψ hg,
    toAdd_unzero_ordFrac_mul (D := R ⧸ q) ((-1 : q.ResidueField) ^ k) (fφ * h) hne
      (mul_ne_zero hfφ hh),
    toAdd_unzero_ordFrac_mul (D := R ⧸ q) fφ h hfφ hh,
    toAdd_unzero_ordFrac_neg_one_pow (D := R ⧸ q) k] at hcong
  have hbk := periodicLength_eq_toAdd_unzero_ordFrac_of_le_ker φ ψ hφψ hψφ q
    hSX hXK hSI hYT hTK hYI hZφ hZψ hmφ hmψ hfinφ hfinψ hfinZ g h fφ fψ hg hh hfφ hfψ
    hgX hhT hδφ hδψ
  have harith := toAdd_unzero_ordFrac_mul_div_mul (D := R ⧸ q) g h fψ fφ hg hh hfψ hfφ
  rw [hbk, ← harith]
  omega

/-- A submodule with a finite-length quotient has a finite-length quotient after passing to any
larger submodule. -/
private theorem isFiniteLength_quotient_of_le {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {Z V : Submodule R M} (hZV : Z ≤ V)
    (hZ : IsFiniteLength R (M ⧸ Z)) : IsFiniteLength R (M ⧸ V) := by
  have hsurj : Function.Surjective
      (Submodule.mapQ Z V LinearMap.id (by simpa using hZV)) := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H w => exact ⟨Submodule.Quotient.mk w, rfl⟩
  exact hZ.of_surjective hsurj

/-- The localization of a submodule, identified with the submodule of the localization that its
image generates. -/
noncomputable def localizedSubtypeEquivRange {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (S : Submonoid R) (P : Submodule R M)
    {Q : Submodule (Localization S) (LocalizedModule S M)}
    (hQ : LinearMap.range (LocalizedModule.map S P.subtype) = Q) :
    LocalizedModule S ↥P ≃ₗ[Localization S] ↥Q :=
  (LinearEquiv.ofInjective (LocalizedModule.map S P.subtype)
      (LocalizedModule.map_injective S P.subtype (Submodule.injective_subtype P))).trans
    (LinearEquiv.ofEq _ _ hQ)

/-- The identification of the localization of a submodule with a submodule of the localization is
the localized inclusion. -/
@[ega "0 1.3.2" "partial"]
theorem subtype_localizedSubtypeEquivRange {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (S : Submonoid R) (P : Submodule R M)
    {Q : Submodule (Localization S) (LocalizedModule S M)}
    (hQ : LinearMap.range (LocalizedModule.map S P.subtype) = Q)
    (c : LocalizedModule S ↥P) :
    Q.subtype (localizedSubtypeEquivRange S P hQ c) = LocalizedModule.map S P.subtype c :=
  rfl

/-- **The five-sequence assembly for Tag 02QD.** Let `(M, φ, ψ)` be a `(2, 1)`-periodic complex
of finite modules over a Noetherian local ring whose localization at a prime `q` with `R / q` of
dimension one is exact and of finite length. Suppose given sequences with successive quotients
`R / q`: `x` spanning a submodule of `ker φ`, `t` spanning a submodule of `ker ψ`, `s` inside the
span of `x` with lifts `st` along `ψ`, `y` inside the span of `t` with lifts `xt` along `φ`, the
concatenations `wφ` of `x` with `xt` and `wψ` of `t` with `st`, and a sequence `z` inside both of
their spans. Then the multiplicity of the complex is minus the order of the periodic determinant
of its localization at `q`. -/
theorem neg_periodicLength_eq_toAdd_unzero_ordFrac_periodicDeterminant_of_sequences
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    (q : Ideal R) [q.IsPrime] [Ring.KrullDimLE 1 (R ⧸ q)]
    (hdim : ringKrullDim (R ⧸ q) = 1)
    (hMq : IsFiniteLength (Localization.AtPrime q) (LocalizedModule q.primeCompl M))
    (hex1 : Function.Exact (LocalizedModule.map q.primeCompl φ)
      (LocalizedModule.map q.primeCompl ψ))
    (hex2 : Function.Exact (LocalizedModule.map q.primeCompl ψ)
      (LocalizedModule.map q.primeCompl φ))
    {b a : ℕ} (x : Fin b → M) (t : Fin a → M) (y : Fin a → M) (s : Fin b → M)
    (xt : Fin a → M) (st : Fin b → M) (wφ wψ z : Fin (b + a) → M)
    (hy : ∀ i, y i = φ (xt i)) (hs : ∀ i, s i = ψ (st i))
    (hwφ : ∀ j, wφ j = Fin.append x xt j)
    (hwψ : ∀ j, wψ j = Fin.append t st (Fin.cast (Nat.add_comm b a) j))
    {X S T Y Vφ Vψ Z : Submodule R M}
    (hX : Submodule.span R (Set.range x) = X)
    (hS : Submodule.span R (Set.range s) = S)
    (hT : Submodule.span R (Set.range t) = T)
    (hY : Submodule.span R (Set.range y) = Y)
    (hVφ : Submodule.span R (Set.range wφ) = Vφ)
    (hVψ : Submodule.span R (Set.range wψ) = Vψ)
    (hZ : Submodule.span R (Set.range z) = Z)
    (hxf : ∀ i : Fin b,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (htf : ∀ i : Fin a,
      Nonempty
        (((spanBefore (R := R) t i ⊔ R ∙ t i : Submodule R M) ⧸
            (spanBefore (R := R) t i).comap
              (spanBefore (R := R) t i ⊔ R ∙ t i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hyf : ∀ i : Fin a,
      Nonempty
        (((spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R M) ⧸
            (spanBefore (R := R) y i).comap
              (spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hsf : ∀ i : Fin b,
      Nonempty
        (((spanBefore (R := R) s i ⊔ R ∙ s i : Submodule R M) ⧸
            (spanBefore (R := R) s i).comap
              (spanBefore (R := R) s i ⊔ R ∙ s i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hwφf : ∀ i : Fin (b + a),
      Nonempty
        (((spanBefore (R := R) wφ i ⊔ R ∙ wφ i : Submodule R M) ⧸
            (spanBefore (R := R) wφ i).comap
              (spanBefore (R := R) wφ i ⊔ R ∙ wφ i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hwψf : ∀ i : Fin (b + a),
      Nonempty
        (((spanBefore (R := R) wψ i ⊔ R ∙ wψ i : Submodule R M) ⧸
            (spanBefore (R := R) wψ i).comap
              (spanBefore (R := R) wψ i ⊔ R ∙ wψ i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hzf : ∀ i : Fin (b + a),
      Nonempty
        (((spanBefore (R := R) z i ⊔ R ∙ z i : Submodule R M) ⧸
            (spanBefore (R := R) z i).comap
              (spanBefore (R := R) z i ⊔ R ∙ z i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hXK : X ≤ LinearMap.ker φ) (hTK : T ≤ LinearMap.ker ψ)
    (hSX : S ≤ X) (hYT : Y ≤ T) (hZφ : Z ≤ Vφ) (hZψ : Z ≤ Vψ)
    (hfinφ : Module.length R (↥(LinearMap.ker φ) ⧸ S.submoduleOf (LinearMap.ker φ)) ≠ ⊤)
    (hfinψ : Module.length R (↥(LinearMap.ker ψ) ⧸ Y.submoduleOf (LinearMap.ker ψ)) ≠ ⊤)
    (hfinX : Module.length R (↥(LinearMap.ker φ) ⧸ X.submoduleOf (LinearMap.ker φ)) ≠ ⊤)
    (hfinT : Module.length R (↥(LinearMap.ker ψ) ⧸ T.submoduleOf (LinearMap.ker ψ)) ≠ ⊤)
    (hfinZ : Module.length R (M ⧸ Z) ≠ ⊤) :
    -periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      Multiplicative.toAdd (WithZero.unzero
        (x := Ring.ordFrac (R ⧸ q)
          ((periodicDeterminant (LocalizedModule.map q.primeCompl φ)
            (LocalizedModule.map q.primeCompl ψ) hex1 hex2 hMq : q.ResidueField)))
        (((periodicDeterminant (LocalizedModule.map q.primeCompl φ)
            (LocalizedModule.map q.primeCompl ψ) hex1 hex2 hMq).isUnit.map
          (Ring.ordFrac (R ⧸ q))).ne_zero)) := by
  subst hX
  subst hS
  subst hT
  subst hY
  subst hVφ
  subst hVψ
  subst hZ
  have hq : q ≠ IsLocalRing.maximalIdeal R := by
    intro hqm
    subst hqm
    have hfield : IsField (R ⧸ IsLocalRing.maximalIdeal R) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
        (IsLocalRing.maximalIdeal.isMaximal R)
    rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact zero_ne_one hdim
  -- the two exact-sequence colength identities, from the concatenated sequences
  have hxmem : ∀ i : Fin b, wφ (Fin.castAdd a i) = x i := fun i ↦ by
    rw [hwφ, Fin.append_left]
  have hxtmem : ∀ i : Fin a, wφ (Fin.natAdd b i) = xt i := fun i ↦ by
    rw [hwφ, Fin.append_right]
  have htmem : ∀ i : Fin a, wψ (Fin.cast (Nat.add_comm a b) (Fin.castAdd b i)) = t i :=
    fun i ↦ by
      rw [hwψ, show Fin.cast (Nat.add_comm b a) (Fin.cast (Nat.add_comm a b) (Fin.castAdd b i))
        = Fin.castAdd b i from Fin.ext rfl, Fin.append_left]
  have hstmem : ∀ i : Fin b, wψ (Fin.cast (Nat.add_comm a b) (Fin.natAdd a i)) = st i :=
    fun i ↦ by
      rw [hwψ, show Fin.cast (Nat.add_comm b a) (Fin.cast (Nat.add_comm a b) (Fin.natAdd a i))
        = Fin.natAdd a i from Fin.ext rfl, Fin.append_right]
  have hXV : Submodule.span R (Set.range x) ≤ Submodule.span R (Set.range wφ) :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Fin.castAdd a i, hxmem i⟩)
  have hTV : Submodule.span R (Set.range t) ≤ Submodule.span R (Set.range wψ) :=
    Submodule.span_mono
      (by rintro _ ⟨i, rfl⟩; exact ⟨Fin.cast (Nat.add_comm a b) (Fin.castAdd b i), htmem i⟩)
  have hmapφ : (Submodule.span R (Set.range wφ)).map φ = Submodule.span R (Set.range y) :=
    (map_span_range_of_append φ rfl x xt wφ (fun j ↦ hwφ j)
      fun i ↦ LinearMap.mem_ker.mp (hXK (Submodule.subset_span ⟨i, rfl⟩))).trans
      (by rw [show (fun i ↦ φ (xt i)) = y from funext fun i ↦ (hy i).symm])
  have hmapψ : (Submodule.span R (Set.range wψ)).map ψ = Submodule.span R (Set.range s) :=
    (map_span_range_of_append ψ (Nat.add_comm b a) t st wψ hwψ
      fun i ↦ LinearMap.mem_ker.mp (hTK (Submodule.subset_span ⟨i, rfl⟩))).trans
      (by rw [show (fun i ↦ ψ (st i)) = s from funext fun i ↦ (hs i).symm])
  have hker_mkQ : ∀ i, (Submodule.span R (Set.range x)).mkQ (x i) = 0 := fun i ↦
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  have hker_mkQ' : ∀ i, (Submodule.span R (Set.range t)).mkQ (t i) = 0 := fun i ↦
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨i, rfl⟩)
  have hVmkQφ := map_span_range_of_append (Submodule.span R (Set.range x)).mkQ rfl x xt wφ
    (fun j ↦ hwφ j) hker_mkQ
  have hVmkQψ := map_span_range_of_append (Submodule.span R (Set.range t)).mkQ
    (Nat.add_comm b a) t st wψ hwψ hker_mkQ'
  have hmφ := length_quotient_eq_ker_add_range_of_isFiniteLength_map_mkQ q hq φ hXV hXK
    (fun i ↦ (Submodule.span R (Set.range x)).mkQ (xt i))
    (primeFiltration_mkQ_of_append rfl q x xt wφ (fun j ↦ hwφ j) hwφf) hVmkQφ
    ((isFiniteLength_map_mkQ (Module.length_ne_top_iff.mp hfinX)).of_injective
      (Submodule.inclusion_injective (Submodule.map_mono inf_le_left)))
  have hmψ := length_quotient_eq_ker_add_range_of_isFiniteLength_map_mkQ q hq ψ hTV hTK
    (fun i ↦ (Submodule.span R (Set.range t)).mkQ (st i))
    (primeFiltration_mkQ_of_append (Nat.add_comm b a) q t st wψ hwψ hwψf) hVmkQψ
    ((isFiniteLength_map_mkQ (Module.length_ne_top_iff.mp hfinT)).of_injective
      (Submodule.inclusion_injective (Submodule.map_mono inf_le_left)))
  rw [hmapφ] at hmφ
  rw [hmapψ] at hmψ
  have hrψ : LinearMap.range (LocalizedModule.map q.primeCompl
      (Submodule.span R (Set.range x)).subtype) =
      LinearMap.range (LocalizedModule.map q.primeCompl ψ) := by
    rw [range_map_subtype_eq_ker_map_of_isFiniteLength_quotient φ q hq hXK
      (Module.length_ne_top_iff.mp hfinX)]
    exact hex2.linearMap_ker_eq
  have hrφ : LinearMap.range (LocalizedModule.map q.primeCompl
      (Submodule.span R (Set.range t)).subtype) =
      LinearMap.range (LocalizedModule.map q.primeCompl φ) := by
    rw [range_map_subtype_eq_ker_map_of_isFiniteLength_quotient ψ q hq hTK
      (Module.length_ne_top_iff.mp hfinT)]
    exact hex1.linearMap_ker_eq
  have hbijφ : Function.Bijective (LocalizedModule.map q.primeCompl
      (Submodule.span R (Set.range wφ)).subtype) :=
    bijective_map_subtype_of_isFiniteLength_quotient q hq _
      (isFiniteLength_quotient_of_le hZφ (Module.length_ne_top_iff.mp hfinZ))
  have hbijψ : Function.Bijective (LocalizedModule.map q.primeCompl
      (Submodule.span R (Set.range wψ)).subtype) :=
    bijective_map_subtype_of_isFiniteLength_quotient q hq _
      (isFiniteLength_quotient_of_le hZψ (Module.length_ne_top_iff.mp hfinZ))
  obtain ⟨hlenU, ss, xs, hss, hxs, hxsspan, g, hg, hgsym, hgcol⟩ :=
    exists_symbol_scalar_localized_span q hdim s x hsf hxf hSX
      (LinearMap.range (LocalizedModule.map q.primeCompl ψ)).subtype
      (localizedSubtypeEquivRange q.primeCompl _ hrψ)
      (subtype_localizedSubtypeEquivRange q.primeCompl _ hrψ)
  obtain ⟨hlenV, ys, ts, hys, hts, htsspan, h, hh, hhsym, hhcol⟩ :=
    exists_symbol_scalar_localized_span q hdim y t hyf htf hYT
      (LinearMap.range (LocalizedModule.map q.primeCompl φ)).subtype
      (localizedSubtypeEquivRange q.primeCompl _ hrφ)
      (subtype_localizedSubtypeEquivRange q.primeCompl _ hrφ)
  obtain ⟨hlenWφ, zsφ, wφs, hzsφ, hwφs, -, fφ, hfφ, hfφsym, hfφcol⟩ :=
    exists_symbol_scalar_localized_span q hdim z wφ hzf hwφf hZφ
      LinearMap.id (LinearEquiv.ofBijective _ hbijφ) (fun _ ↦ rfl)
  obtain ⟨hlenWψ, zsψ, wψs, hzsψ, hwψs, -, fψ, hfψ, hfψsym, hfψcol⟩ :=
    exists_symbol_scalar_localized_span q hdim z wψ hzf hwψf hZψ
      LinearMap.id (LinearEquiv.ofBijective _ hbijψ) (fun _ ↦ rfl)
  have hzeq : zsφ = zsψ :=
    admissibleSequence_ext LinearMap.id Function.injective_id fun j ↦ by
      rw [hzsφ j, hzsψ j]
  have hKψ : IsFiniteLength (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl ψ)) :=
    hMq.of_injective (Submodule.injective_subtype _)
  have hKφ : IsFiniteLength (Localization.AtPrime q)
      ↥(LinearMap.range (LocalizedModule.map q.primeCompl φ)) :=
    hMq.of_injective (Submodule.injective_subtype _)
  have hxs0 : symbol xs ≠ 0 := symbol_ne_zero_of_span_top hKψ xs hxsspan
  have hts0 : symbol ts ≠ 0 := symbol_ne_zero_of_span_top hKφ ts htsspan
  have hys0 : symbol ys ≠ 0 := by rw [hhsym]; exact smul_ne_zero hh hts0
  have hss0 : symbol ss ≠ 0 := by rw [hgsym]; exact smul_ne_zero hg hxs0
  have hγφ := periodicGamma_symbol_tmul_symbol φ ψ q hMq hex2 (rfl : b + a = b + a) x xt
    xs ys wφs hlenU hlenV hlenWφ hxs (fun i ↦ by rw [hys i, hy])
    (fun j ↦ by
      have hj : wφs.1 j = LocalizedModule.mk (wφ (Fin.cast hlenWφ j)) 1 := hwφs j
      rw [hj, hwφ]) hxs0 hys0
  have hγψ := periodicGamma_symbol_tmul_symbol ψ φ q hMq hex1 (Nat.add_comm b a) t st
    ts ss wψs hlenV hlenU hlenWψ hts (fun i ↦ by rw [hss i, hs])
    (fun j ↦ by
      have hj : wψs.1 j = LocalizedModule.mk (wψ (Fin.cast hlenWψ j)) 1 := hwψs j
      rw [hj, hwψ, show Fin.cast (Nat.add_comm b a) (Fin.cast hlenWψ j) =
        Fin.cast (hlenWψ.trans (Nat.add_comm b a)) j from Fin.ext rfl]) hts0 hss0
  have hzz : fφ • periodicGamma (LocalizedModule.map q.primeCompl φ)
          (LocalizedModule.map q.primeCompl ψ) hex2 hMq
          (symbol xs ⊗ₜ[q.ResidueField] symbol ys) =
      fψ • periodicGamma (LocalizedModule.map q.primeCompl ψ)
          (LocalizedModule.map q.primeCompl φ) hex1 hMq
          (symbol ts ⊗ₜ[q.ResidueField] symbol ss) := by
    rw [hγφ, hγψ, ← hfφsym, ← hfψsym, hzeq]
  exact neg_periodicLength_eq_toAdd_unzero_ordFrac_periodicDeterminant φ ψ hφψ hψφ q hMq
    hex1 hex2 hSX hXK
    (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨st i, (hs i).symm⟩))
    hYT hTK
    (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨xt i, (hy i).symm⟩))
    hZφ hZψ hmφ hmψ hfinφ hfinψ hfinZ xs ss ts ys hxsspan htsspan g h fφ fψ hg hh hfφ hfψ
    hhsym hgsym hzz hgcol hhcol hfφcol hfψcol

end AlgebraicGeometry

end
