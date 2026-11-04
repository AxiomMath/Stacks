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
public import StacksFrontier.AlgebraicGeometry.Chow.LengthsDeterminants.PrimeFiltrations.ElementaryOperations
public import StacksFrontier.AlgebraicGeometry.Chow.LengthsDeterminants.PrimeFiltrations.PrimeFactors
import all StacksFrontier.AlgebraicGeometry.Chow.LengthsDeterminants.PrimeFiltrations.ElementaryOperations
import all StacksFrontier.AlgebraicGeometry.Chow.LengthsDeterminants.PrimeFiltrations.PrimeFactors

/-!
# Injectivity at a one-dimensional prime

Let `q` be a prime of a Noetherian local ring such that `R / q` has dimension one. For maps
between finite modules equipped with filtrations whose successive factors are `R / q`,
injectivity can be detected after localization at `q`. This file proves that criterion,
together with the comparisons the length formula of Tag 02QB is built from: the symbols of two
localized filtrations differ by the residue of a pivot scalar, and the colength of a map
taking the entries of one filtration to scalar multiples of those of another is the sum of the
orders of vanishing of the scalars.

## Main results

* `Module.FiniteLength.injective_iff_localizedMap_bijective_of_prime_filtrations` detects
  injectivity after localization.

## Implementation notes

Localization is represented by `LocalizedModule`, and an isomorphism of localized modules by
bijectivity of the canonical localized linear map.

## References

* [Stacks Project, Tag 02QB](https://stacks.math.columbia.edu/tag/02QB)
-/

@[expose] public section

noncomputable section

namespace Module.FiniteLength

universe u v w

/-- The symbols of two localized filtrations differ by the residue of the pivot scalar times
the scalar comparing the filtrations one step shorter. -/
private theorem symbol_localized_eq_residue_mul_smul
    {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    (q : Ideal R) [q.IsPrime] {l : ℕ} (x y : Fin (l + 1) → N)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (hyf : ∀ i r, r • y i ∈ spanBefore (R := R) y i ↔ r ∈ q)
    (a : R) (ha : a ∉ q) (hxy : x 0 = a • y 0)
    (eX eY : AdmissibleSequence (Localization.AtPrime q) (LocalizedModule q.primeCompl N))
    (hL : moduleLength (Localization.AtPrime q) (LocalizedModule q.primeCompl N) = l + 1)
    (heX : ∀ i, eX.1 i = LocalizedModule.mk (x (Fin.cast hL i)) 1)
    (heY : ∀ i, eY.1 i = LocalizedModule.mk (y (Fin.cast hL i)) 1)
    (eQX eQY : AdmissibleSequence (Localization.AtPrime q)
      (LocalizedModule q.primeCompl (N ⧸ (R ∙ y 0))))
    (hQ : moduleLength (Localization.AtPrime q)
      (LocalizedModule q.primeCompl (N ⧸ (R ∙ y 0))) = l)
    (heQX : ∀ i, eQX.1 i = LocalizedModule.mk
      ((R ∙ y 0).mkQ (x (Fin.cast hQ i).succ)) 1)
    (heQY : ∀ i, eQY.1 i = LocalizedModule.mk
      ((R ∙ y 0).mkQ (y (Fin.cast hQ i).succ)) 1)
    (b : IsLocalRing.ResidueField (Localization.AtPrime q)) (hb : b ≠ 0)
    (hdet : symbol eQX = b • symbol eQY) :
    symbol eX = (IsLocalRing.residue (Localization.AtPrime q)
      (algebraMap R (Localization.AtPrime q) a) * b) • symbol eY := by
  classical
  let S := Localization.AtPrime q
  let V := R ∙ y 0
  let K := LocalizedModule q.primeCompl V
  let L := LocalizedModule q.primeCompl N
  let Q := LocalizedModule q.primeCompl (N ⧸ V)
  let i : K →ₗ[S] L := LocalizedModule.map q.primeCompl V.subtype
  let p : L →ₗ[S] Q := LocalizedModule.map q.primeCompl V.mkQ
  have hi : Function.Injective i :=
    LocalizedModule.map_injective _ _ (Submodule.subtype_injective _)
  have hp : Function.Surjective p := LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _)
  have hip : Function.Exact i p := LocalizedModule.map_exact _ _ _ (by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype])
  have hfirst : spanPrefix (R := R) y 1 = V := by
    rw [spanPrefix_succ y 0 (by omega)]
    simp [spanPrefix, V]
  have hKlen : Module.length S K = 1 := by
    have h := localized_length_spanPrefix q y
      (fun j => cyclic_factor_equiv_of_smul_mem_iff _ _ q (hyf j)) 1 (by omega)
    rwa [hfirst] at h
  have hK : IsFiniteLength S K := Module.length_ne_top_iff.mp (by rw [hKlen]; simp)
  have hLlen : Module.length S L = l + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using localized_length_of_generating q y hy
      (fun j => cyclic_factor_equiv_of_smul_mem_iff _ _ q (hyf j))
  have hLf : IsFiniteLength S L := Module.length_ne_top_iff.mp (by rw [hLlen]; simp)
  have hQf : IsFiniteLength S Q := Module.length_ne_top_iff.mp
    (ne_top_of_le_ne_top (Module.length_ne_top_iff.mpr hLf) (Module.length_le_of_surjective p hp))
  have hKn : moduleLength S K = 1 := by simp only [moduleLength, hKlen, ENat.toNat_one]
  let v : V := ⟨y 0, Submodule.mem_span_singleton_self _⟩
  let z : K := LocalizedModule.mk v 1
  have hvg : R ∙ v = ⊤ := span_cyclic_submodule_generator _
  have hzgen : S ∙ z = ⊤ := by
    have h := span_localized_generators_eq_top q.primeCompl (fun _ : Unit => v) (by simpa using hvg)
    simpa only [Set.range_const] using h
  have hvann : Module.annihilator R V = q := annihilator_first_span q y hyf
  have hzad : IsAdmissibleSequence (R := S) (fun _ : Fin 1 => z) :=
    admissible_localized q (fun _ : Fin 1 => v) (by
      intro j r hr
      have h0 : r • v = 0 := Module.mem_annihilator.mp (hvann.symm ▸ hr) _
      rw [h0]
      exact Submodule.zero_mem _)
  let eK : AdmissibleSequence S K :=
    ⟨fun _ => z, admissible_cast hKn (fun _ : Fin 1 => z) hzad⟩
  have heK : symbol eK ≠ 0 := symbol_ne_zero_of_generating hK eK (by
    have : Nonempty (Fin (moduleLength S K)) := ⟨⟨0, by omega⟩⟩
    simpa only [eK, Set.range_const] using hzgen)
  obtain ⟨au, hau⟩ :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S q a).mpr ha
  let eKa : AdmissibleSequence S K :=
    ⟨fun j => (au : S) • eK.1 j, admissible_units_smul eK.1 eK.2 (fun _ => au)⟩
  have hKa : symbol eKa = IsLocalRing.residue S (algebraMap R S a) • symbol eK := by
    rw [symbol_units_smul]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hKn, pow_one, hau]
  have hres : IsLocalRing.residue S (algebraMap R S a) ≠ 0 := by
    rw [← hau]
    exact (Units.isUnit au |>.map (IsLocalRing.residue S)).ne_zero
  have heKa : symbol eKa ≠ 0 := by rw [hKa]; exact smul_ne_zero hres heK
  have hyQgen : Submodule.span S (Set.range eQY.1) = ⊤ := by
    have hgen := span_localized_generators_eq_top q.primeCompl
      (fun j : Fin l => V.mkQ (y j.succ)) (span_quotient_tail_eq_top y hy)
    rw [← (Fin.castOrderIso hQ).surjective.range_comp] at hgen
    convert hgen using 3
    exact funext heQY
  have heQY0 : symbol eQY ≠ 0 := symbol_ne_zero_of_generating hQf eQY hyQgen
  have heQX0 : symbol eQX ≠ 0 := by rw [hdet]; exact smul_ne_zero hb heQY0
  let tx : Fin (moduleLength S Q) → L :=
    fun j => LocalizedModule.mk (x (Fin.cast hQ j).succ) 1
  let ty : Fin (moduleLength S Q) → L :=
    fun j => LocalizedModule.mk (y (Fin.cast hQ j).succ) 1
  have htx (j) : p (tx j) = eQX.1 j :=
    (LocalizedModule.map_mk q.primeCompl V.mkQ _ _).trans (heQX j).symm
  have hty (j) : p (ty j) = eQY.1 j :=
    (LocalizedModule.map_mk q.primeCompl V.mkQ _ _).trans (heQY j).symm
  change moduleLength S L = l + 1 at hL
  change moduleLength S Q = l at hQ
  have hlen : moduleLength S L = moduleLength S K + moduleLength S Q := by omega
  have hcons (e : AdmissibleSequence S L) (w : Fin (l + 1) → N)
      (he : ∀ j, e.1 j = LocalizedModule.mk (w (Fin.cast hL j)) 1)
      (t : Fin (moduleLength S Q) → L)
      (ht : ∀ j, t j = LocalizedModule.mk (w (Fin.cast hQ j).succ) 1)
      (z' : K) (hz' : i z' = LocalizedModule.mk (w 0) 1) (j) :
      e.1 j = Fin.append (fun _ : Fin (moduleLength S K) => i z') t (Fin.cast hlen j) := by
    generalize hj : Fin.cast hlen j = j'
    have hj' : j = Fin.cast hlen.symm j' := by rw [← hj]; rfl
    subst j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j'
    · rw [Fin.append_left, he, hz']
      congr 2
      apply Fin.ext
      have := k.isLt
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_zero]
      omega
    · rw [Fin.append_right, he, ht]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      omega
  have hiz : i z = LocalizedModule.mk (y 0) 1 :=
    LocalizedModule.map_mk q.primeCompl V.subtype v 1
  apply symbol_append_eq_mul_smul_of_exact i p hi hp hip hK hLf hQf
    eKa eK eQX eQY heKa heK heQX0 heQY0 eX eY tx ty htx hty hlen
  · intro j
    exact hcons eX x heX tx (fun _ => rfl) ((au : S) • z) (by
      rw [map_smul, hau, IsScalarTower.algebraMap_smul, hxy]
      rw [hiz, LocalizedModule.smul'_mk]) j
  · intro j
    exact hcons eY y heY ty (fun _ => rfl) z hiz j
  · exact hKa
  · exact hdet

/-- The colength of the ideal generated by `a` together with `q` is the order of vanishing of
`a` on the domain `R / q`. -/
private theorem length_quotient_sup_eq_ord_quotient
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime] (a : R) :
    Module.length R (R ⧸ (Ideal.span {a} ⊔ q)) =
      Ring.ord (R ⧸ q) (Ideal.Quotient.mk q a) := by
  let D := R ⧸ q
  let T : Submodule R R := Ideal.span {a}
  let E := Submodule.quotientQuotientEquivQuotientSup (M := R) q T
  let J : Submodule D D := Ideal.span {Ideal.Quotient.mk q a}
  let X := D ⧸ J
  have hmap : T.map (Submodule.mkQ q) = J.restrictScalars R := by
    ext z
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      change w ∈ Ideal.span {a} at hw
      rw [Ideal.mem_span_singleton] at hw
      rcases hw with ⟨c, rfl⟩
      show Ideal.Quotient.mk q (a * c) ∈
        Ideal.span {Ideal.Quotient.mk q a}
      rw [Ideal.mem_span_singleton]
      exact ⟨Ideal.Quotient.mk q c, by simp [map_mul]⟩
    · intro hz
      change z ∈ Ideal.span {Ideal.Quotient.mk q a} at hz
      rw [Ideal.mem_span_singleton] at hz
      rcases hz with ⟨c, hc⟩
      obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (I := q) c
      refine ⟨a * c', ?_, ?_⟩
      · rw [Ideal.mem_span_singleton]
        exact ⟨c', rfl⟩
      · show Ideal.Quotient.mk q (a * c') = z
        rw [map_mul, hc']
        exact hc.symm
  have hE : Module.length R (R ⧸ (Ideal.span {a} ⊔ q)) =
      Module.length R (D ⧸ T.map (Submodule.mkQ q)) := by
    have hsup : Ideal.span {a} ⊔ q = q ⊔ T := by
      rw [show Ideal.span {a} = T by rfl, sup_comm]
    rw [hsup]
    exact E.length_eq.symm
  let : IsScalarTower R D X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hres : Module.length R X = Module.length D X :=
    Module.length_eq_of_surjective (S := R) (R := D) (M := X) Ideal.Quotient.mk_surjective
  have e' : (D ⧸ T.map (Submodule.mkQ q)) ≃ₗ[R] X :=
    Submodule.quotEquivOfEq (T.map (Submodule.mkQ q)) (J.restrictScalars R) hmap
  calc
    Module.length R (R ⧸ (Ideal.span {a} ⊔ q))
        = Module.length R (D ⧸ T.map (Submodule.mkQ q)) := hE
    _ = Module.length R X := e'.length_eq
    _ = Module.length D X := hres
    _ = Ring.ord D (Ideal.Quotient.mk q a) := rfl

/-- A map between cyclic modules with annihilator `q` sending generator to a scalar multiple of
generator, with the scalar outside `q`, is injective. -/
private theorem injective_of_scalar_generators
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (q : Ideal R) [q.IsPrime] (x : M) (y : N)
    (hx : R ∙ x = ⊤) (hy : R ∙ y = ⊤)
    (hxann : Module.annihilator R M = q) (hyann : Module.annihilator R N = q)
    (φ : M →ₗ[R] N) (a : R) (ha : a ∉ q) (hφ : φ x = a • y) :
    Function.Injective φ := by
  apply (LinearMap.ker_eq_bot).mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨r, rfl⟩ := (Submodule.span_singleton_eq_top_iff R x).mp hx z
  have hmul : r * a ∈ q := by
    rw [← hyann, scalar_mem_annihilator_iff_of_generator y hy]
    simpa only [LinearMap.mem_ker, map_smul, hφ, smul_smul] using hz
  have hr : r ∈ Module.annihilator R M := hxann.symm ▸
    ((Ideal.IsPrime.mem_or_mem ‹q.IsPrime› hmul).resolve_right ha)
  exact Module.mem_annihilator.mp hr x

/-- For such a map, the colength is the order of vanishing of that scalar. -/
private theorem length_coker_eq_ord_of_scalar_generators
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (q : Ideal R) [q.IsPrime] (x : M) (y : N)
    (hx : R ∙ x = ⊤) (hy : R ∙ y = ⊤)
    (hyann : Module.annihilator R N = q)
    (φ : M →ₗ[R] N) (a : R) (hφ : φ x = a • y) :
    Module.length R (N ⧸ LinearMap.range φ) = Ring.ord (R ⧸ q) (Ideal.Quotient.mk q a) := by
  have hrange : LinearMap.range φ = R ∙ (a • y) := by
    rw [← Submodule.map_top, ← hx, Submodule.map_span, Set.image_singleton, hφ]
  rw [hrange, length_quotient_span_smul q y hy hyann,
    length_quotient_sup_eq_ord_quotient]

/-- For a map taking each entry of one filtration to the same scalar multiple of the
corresponding entry of the other, the colength is the sum of the orders of those scalars. -/
private theorem length_coker_eq_sum_ord_of_diagonal
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (q : Ideal R) [q.IsPrime] (l : ℕ) (x : Fin l → M) (y : Fin l → N)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hxf : ∀ i r, r • x i ∈ spanBefore (R := R) x i ↔ r ∈ q)
    (hy : Submodule.span R (Set.range y) = ⊤)
    (hyf : ∀ i r, r • y i ∈ spanBefore (R := R) y i ↔ r ∈ q)
    (φ : M →ₗ[R] N) (hφ : Function.Injective φ)
    (a : Fin l → R) (ha : ∀ i, a i ∉ q) (hdiag : ∀ i, φ (x i) = a i • y i) :
    Module.length R (N ⧸ LinearMap.range φ) =
      ∑ i, Ring.ord (R ⧸ q) (Ideal.Quotient.mk q (a i)) := by
  induction l generalizing M N with
  | zero =>
    have hbot : (⊥ : Submodule R N) = ⊤ := by simpa using hy
    have : Subsingleton N := (Submodule.subsingleton_iff R).mp
      (subsingleton_of_bot_eq_top hbot)
    simp
  | succ l ih =>
    let U := R ∙ x 0
    let V := R ∙ y 0
    have hUV : U ≤ V.comap φ := by
      apply Submodule.span_le.mpr
      rintro z (rfl : z = x 0)
      show φ (x 0) ∈ V
      rw [hdiag]
      exact V.smul_mem _ (Submodule.mem_span_singleton_self _)
    let ψ := U.mapQ V φ hUV
    have hψ : Function.Injective ψ :=
      injective_quotient_map_of_first_scalar q x (y 0) hx hxf φ hφ (a 0) (ha 0)
        (hdiag 0) hUV
    let xb : Fin l → M ⧸ U := fun i => U.mkQ (x i.succ)
    let yb : Fin l → N ⧸ V := fun i => V.mkQ (y i.succ)
    have htail := ih xb yb (span_quotient_tail_eq_top x hx)
      (prime_factors_quotient_tail q x hxf) (span_quotient_tail_eq_top y hy)
      (prime_factors_quotient_tail q y hyf) ψ hψ (fun i => a i.succ) (fun i => ha i.succ)
      (fun i => by
        show V.mkQ (φ (x i.succ)) = a i.succ • V.mkQ (y i.succ)
        rw [hdiag, map_smul])
    let φU := (φ.domRestrict U).codRestrict V (fun z => hUV z.property)
    let xU : U := ⟨x 0, Submodule.mem_span_singleton_self _⟩
    let yV : V := ⟨y 0, Submodule.mem_span_singleton_self _⟩
    have hfirst : Module.length R (V ⧸ LinearMap.range φU) =
        Ring.ord (R ⧸ q) (Ideal.Quotient.mk q (a 0)) :=
      length_coker_eq_ord_of_scalar_generators q xU yV
        (span_cyclic_submodule_generator _) (span_cyclic_submodule_generator _)
        (annihilator_first_span q y hyf) φU (a 0) (Subtype.ext (hdiag 0))
    rw [length_coker_eq_add_of_quotient_injective U V φ hUV hψ, hfirst, htail,
      Fin.sum_univ_succ]

/-- A sum that is `0` below a cut-off and `d` above it is a multiple of `d`. -/
private theorem sum_fin_suffix
    {A : Type*} [AddCommMonoid A] (d : A) (l k : ℕ) :
    (∑ i : Fin l, if i.val < k then 0 else d) = (l - k) • d := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases h : l < k
    · simp [h, show l - k = 0 by omega, show l + 1 - k = 0 by omega]
    · rw [ite_eq_right h, show l + 1 - k = (l - k) + 1 by omega, add_nsmul, one_nsmul]

/-- Scaling the tail of a generating filtration beyond a cut-off multiplies the colength of the
resulting submodule by the number of scaled entries. -/
private theorem length_quotient_scale_suffix
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {l : ℕ} (q : Ideal R) [q.IsPrime] (x : Fin l → M)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hxf : ∀ i r, r • x i ∈ spanBefore (R := R) x i ↔ r ∈ q)
    (a : R) (ha : a ∉ q) (k : ℕ) :
    Module.length R (M ⧸ Submodule.span R
      (Set.range (fun i => if i.val < k then x i else a • x i))) =
        (l - k) • Ring.ord (R ⧸ q) (Ideal.Quotient.mk q a) := by
  classical
  let xs : Fin l → M := fun i => if i.val < k then x i else a • x i
  let P := Submodule.span R (Set.range xs)
  have hxs (i : Fin l) : xs i ∈ P := Submodule.subset_span ⟨i, rfl⟩
  let xp : Fin l → P := fun i => ⟨xs i, hxs i⟩
  have hxp : Submodule.span R (Set.range xp) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff P hxs).mpr rfl
  have hxpf : ∀ i r, r • xp i ∈ spanBefore (R := R) xp i ↔ r ∈ q := by
    intro i r
    rw [← prime_factors_map_iff xp P.subtype (Submodule.subtype_injective _) i r]
    exact prime_factors_scale_suffix q x hxf a ha k i r
  have h := length_coker_eq_sum_ord_of_diagonal q l xp x hxp hxpf hx hxf
    P.subtype (Submodule.subtype_injective _)
    (fun i => if i.val < k then 1 else a)
    (fun i => by
      split_ifs
      · exact fun h =>
          (Ideal.IsPrime.ne_top ‹q.IsPrime›) (Ideal.eq_top_of_isUnit_mem q h isUnit_one)
      · exact ha)
    (fun i => by
      show (if i.val < k then x i else a • x i) = (if i.val < k then 1 else a) • x i
      split_ifs <;> simp)
  rw [Submodule.range_subtype] at h
  show Module.length R (M ⧸ P) = _
  rw [h]
  have heq (i : Fin l) : Ring.ord (R ⧸ q) (Ideal.Quotient.mk q (if i.val < k then 1 else a)) =
      if i.val < k then 0 else Ring.ord (R ⧸ q) (Ideal.Quotient.mk q a) := by
    split_ifs <;> simp
  simp_rw [heq]
  exact sum_fin_suffix _ l k

/-- If a map is surjective after localization, some element of the monoid carries every entry
of a finite family into its range. -/
private theorem exists_smul_generators_mem_range
    {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (S : Submonoid R) {l : ℕ} (y : Fin l → N) (φ : M →ₗ[R] N)
    (hφ : Function.Surjective (LocalizedModule.map S φ)) :
    ∃ a : S, ∀ i, (a : R) • y i ∈ LinearMap.range φ := by
  classical
  have hzero : Subsingleton (LocalizedModule S (N ⧸ LinearMap.range φ)) :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker S φ).mp hφ
  have h := LocalizedModule.subsingleton_iff.mp hzero
  have hex (i : Fin l) : ∃ a : S, (a : R) • y i ∈ LinearMap.range φ := by
    obtain ⟨a, ha, haz⟩ := h ((LinearMap.range φ).mkQ (y i))
    refine ⟨⟨a, ha⟩, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    show (LinearMap.range φ).mkQ (a • y i) = 0
    rw [map_smul]
    exact haz
  choose a ha using hex
  refine ⟨∏ i, a i, fun i => ?_⟩
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  show (↑(∏ j, a j) : R) • y i ∈ LinearMap.range φ
  rw [hb, Submonoid.coe_mul, mul_smul, smul_comm]
  exact Submodule.smul_mem _ (b : R) (ha i)

/-- The colength of a map that is surjective after localization at `q` is finite. -/
private theorem length_coker_ne_top_of_localized_surjective
    {R : Type*} [CommRing R] [IsNoetherianRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (q : Ideal R) [q.IsPrime] [Ring.KrullDimLE 1 (R ⧸ q)]
    {l : ℕ} (y : Fin l → N) (hy : Submodule.span R (Set.range y) = ⊤)
    (hyf : ∀ i r, r • y i ∈ spanBefore (R := R) y i ↔ r ∈ q)
    (φ : M →ₗ[R] N) (hφ : Function.Surjective (LocalizedModule.map q.primeCompl φ)) :
    Module.length R (N ⧸ LinearMap.range φ) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_smul_generators_mem_range q.primeCompl y φ hφ
  let P := Submodule.span R (Set.range (fun i => (a : R) • y i))
  have hP : P ≤ LinearMap.range φ := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact ha i)
  let g := P.mapQ (LinearMap.range φ) LinearMap.id (by simpa using hP)
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φ) z
    exact ⟨P.mkQ n, rfl⟩
  apply ne_top_of_le_ne_top _ (Module.length_le_of_surjective g hg)
  have hlen := length_quotient_scale_suffix q y hy hyf (a : R) a.property 0
  have hs : (fun i : Fin l => if i.val < 0 then y i else (a : R) • y i) =
      (fun i => (a : R) • y i) := by funext i; simp
  rw [hs, Nat.sub_zero] at hlen
  show Module.length R (N ⧸ P) ≠ ⊤
  rw [hlen, nsmul_eq_mul]
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Ring.ord_ne_top
    (mem_nonZeroDivisors_of_ne_zero (Ideal.Quotient.eq_zero_iff_mem.not.mpr a.property)))

/-- The order of the fraction attached to a nonzero ring element is its order of vanishing. -/
private theorem ordFrac_algebraMap_eq_length
    {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [Ring.KrullDimLE 1 D] {K : Type v} [Field K] [Algebra D K] [IsFractionRing D K]
    (a : D) (ha : a ≠ 0) (hmap : algebraMap D K a ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero
      (x := Ring.ordFrac D (algebraMap D K a))
      ((isUnit_iff_ne_zero.mpr hmap).map (Ring.ordFrac D)).ne_zero) =
      ((Module.length D (D ⧸ Ideal.span {a})).toNat : ℤ) := by
  let n := (Module.length D (D ⧸ Ideal.span {a})).toNat
  have ha' : a ∈ nonZeroDivisors D := mem_nonZeroDivisors_of_ne_zero ha
  have hfrac : Ring.ordFrac D (algebraMap D K a) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hmap).map (Ring.ordFrac D)).ne_zero
  have hord_ne : Ring.ord D a ≠ ⊤ := by
    intro htop
    have hzero : Ring.ordMonoidWithZeroHom D a = 0 := by
      simp [Ring.ordMonoidWithZeroHom, ha', htop]
    rw [Ring.ordFrac_eq_ord D (x := a) ha, hzero] at hfrac
    exact hfrac rfl
  have hord : Ring.ord D a = (n : ℕ∞) := by
    dsimp [n]
    rw [show Ring.ord D a = Module.length D (D ⧸ Ideal.span {a}) by rfl]
    exact (ENat.natCast_toNat hord_ne).symm
  have hvalue : Ring.ordMonoidWithZeroHom D a =
      ((Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [Ring.ordMonoidWithZeroHom, ha', hord]
  have hunzero : WithZero.unzero hfrac = Multiplicative.ofAdd (n : ℤ) := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, Ring.ordFrac_eq_ord D (x := a) ha,
      hvalue]
  rw [hunzero]
  simp [n]

/-- A map between modules with equally long filtrations by `R / q` is injective exactly when
its localization at `q` is an isomorphism. -/
@[stacks 02QB "injectivity criterion"]
theorem injective_iff_localizedMap_bijective_of_prime_filtrations
    {R : Type u} {M : Type v} {N : Type w} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (q : Ideal R) [q.IsPrime] (l : ℕ) (x : Fin l → M) (y : Fin l → N)
    (hx : Submodule.span R (Set.range x) = ⊤)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (hy : Submodule.span R (Set.range y) = ⊤)
    (hyf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R N) ⧸
            (spanBefore (R := R) y i).comap
              (spanBefore (R := R) y i ⊔ R ∙ y i : Submodule R N).subtype) ≃ₗ[R]
          R ⧸ q))
    (φ : M →ₗ[R] N) :
    Function.Injective φ ↔
      Function.Bijective (LocalizedModule.map q.primeCompl φ) := by
  constructor
  · intro hφ
    have hlocalInj := LocalizedModule.map_injective q.primeCompl φ hφ
    have hM := localized_length_of_generating q x hx hxf
    have hN := localized_length_of_generating q y hy hyf
    exact ⟨hlocalInj,
      surjective_of_injective_of_length_eq (LocalizedModule.map q.primeCompl φ)
        l hlocalInj hM hN⟩
  · intro hφ
    have hprefix := associatedPrimes_spanPrefix_subset q x hxf l le_rfl
    have htop := spanPrefix_eq_top_of_generating x hx
    let eTop : spanPrefix (R := R) x l ≃ₗ[R] M :=
      (LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv
    have hass : associatedPrimes R M ⊆ {q} := by
      rw [LinearEquiv.AssociatedPrimes.eq eTop.symm]
      exact hprefix
    exact injective_of_localized_injective_of_associatedPrimes_subset
      q φ hass hφ.1

end Module.FiniteLength
