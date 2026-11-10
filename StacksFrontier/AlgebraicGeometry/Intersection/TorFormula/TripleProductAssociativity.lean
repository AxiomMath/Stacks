module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.RingTheory.Length
public import StacksFrontier.Algebra.Homology.Resolution.Defs.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedTensor
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.Tor
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.SerreMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafVanishing
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.RingTheory.Tor.Finiteness
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the triple intersection product

Let `A` be a regular local ring of dimension at most `n` and let `M`, `N`, `P` be finite
`A`-modules whose supports meet only in the maximal ideal. The two alternating double sums

`∑ᵢⱼ (-1)ⁱ⁺ʲ length Torᵢᴬ(M, Torⱼᴬ(N, P))`  and  `∑ᵢⱼ (-1)ⁱ⁺ʲ length Torᵢᴬ(Torⱼᴬ(M, N), P)`

are equal: both compute the Euler characteristic of the triple derived tensor product
`M ⊗ᴸ N ⊗ᴸ P`. For `A` the local ring of a nonsingular variety `X` at the generic point of a
component `Z` of `U ∩ V ∩ W` and `M`, `N`, `P` the local rings of three closed subvarieties
`U`, `V`, `W` meeting properly, the two sides are the coefficients of `Z` in `U · (V · W)` and
in `(U · V) · W`.

## Main results

* `Stacks.Intersection.finsum_alternating_length_tor_assoc` — the identity of the two
  alternating double sums, under finiteness and vanishing hypotheses on the iterated `Tor`
  modules.
* `Stacks.Intersection.finsum_alternating_length_tor_assoc_of_isRegularLocalRing` — the same
  over a regular local ring of dimension at most `n`, for finite modules whose supports meet
  only in the maximal ideal, where both the vanishing and the finiteness of the lengths are
  automatic.
* `Stacks.Intersection.finsum_alternating_length_tor_assoc_quotient` — the case of the three
  local rings `A ⧸ I`, `A ⧸ J`, `A ⧸ K` of three closed subvarieties.

## Implementation notes

Each iterated sum is read as the `E₂`-page of one of the two spectral sequences of the derived
tensor product of `M` with `N ⊗ᴸ P`, respectively of `M ⊗ᴸ N` with `P`; both abut to the
cohomology of the triple derived tensor product, and the two abutments are identified by the
associator. Since length is additive on short exact sequences, the alternating sum of the
lengths of the entries of a page is unchanged by turning the page, and equals the alternating
sum of the lengths of the cohomology of the abutment. Lengths are `ℕ∞`-valued and the
alternating sums are formed in `ℤ` after `ENat.toNat`, which is faithful exactly where the
lengths are finite; that is what the finiteness hypotheses provide.

The sums are indexed by `ℕ × ℕ` and the spectral sequences by `ℤ × ℤ`; the two are matched by
negating the indices, using that `Tor` in a negative degree is the zero module.

## References

* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Intersection

section EulerCharacteristic

universe v

open CategoryTheory.Limits

private lemma length_shortComplex (R : Type u) [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) :
    Module.length R S.X₂ = Module.length R S.homology +
      Module.length R (LinearMap.range S.f.hom) +
      Module.length R (LinearMap.range S.g.hom) := by
  have h₁ := Module.length_eq_add_of_exact (LinearMap.ker S.g.hom).subtype
    S.g.hom.rangeRestrict (Submodule.subtype_injective _)
    S.g.hom.surjective_rangeRestrict (LinearMap.exact_iff.mpr (by simp))
  have h₂ := Module.length_eq_add_of_exact
    (LinearMap.range S.moduleCatToCycles).subtype
    (LinearMap.range S.moduleCatToCycles).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_iff.mpr (by simp))
  have he : Module.length R (LinearMap.range S.moduleCatToCycles) =
      Module.length R (LinearMap.range S.f.hom) := by
    rw [← S.moduleCatToCycles.quotKerEquivRange.length_eq,
      ← S.f.hom.quotKerEquivRange.length_eq]
    have hk : S.moduleCatToCycles.ker = S.f.hom.ker := by
      ext x
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hk]
  have hH : Module.length R S.homology =
      Module.length R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.length_eq
  rw [h₁, h₂, he, hH]
  ac_rfl
private lemma intLength_shortComplex (R : Type u) [Ring R]
    (S : ShortComplex (ModuleCat.{v} R)) (h : Module.length R S.X₂ ≠ ⊤) :
    ((Module.length R S.X₂).toNat : ℤ) =
      ((Module.length R S.homology).toNat : ℤ) +
      ((Module.length R (LinearMap.range S.f.hom)).toNat : ℤ) +
      ((Module.length R (LinearMap.range S.g.hom)).toNat : ℤ) := by
  have he := length_shortComplex R S
  rw [he, ne_eq, ENat.add_eq_top, ENat.add_eq_top, not_or, not_or] at h
  rw [he, ENat.toNat_add (by simp [h]) h.2,
    ENat.toNat_add h.1.1 h.1.2, Nat.cast_add, Nat.cast_add]
private lemma finsum_eq_of_add_sub_equiv {ι : Type*}
    (a h b : ι → ℤ) (e : ι ≃ ι)
    (hh : (Function.support h).Finite) (hb : (Function.support b).Finite)
    (he : ∀ i, a i = h i + b i - b (e i)) :
    ∑ᶠ i, a i = ∑ᶠ i, h i := by
  have hbe : (Function.support (fun i => b (e i))).Finite :=
    hb.preimage e.injective.injOn
  have hhb : (Function.support (fun i => h i + b i)).Finite :=
    (hh.union hb).subset (Function.support_add _ _)
  simp_rw [he]
  rw [finsum_sub_distrib hhb hbe, finsum_add_distrib hh hb,
    finsum_comp_equiv e]
  abel

/-- A zero module has length zero. -/
private lemma length_eq_zero_of_isZero (R : Type u) [Ring R] {Z : ModuleCat.{v} R}
    (h : IsZero Z) : Module.length R Z = 0 := by
  have := ModuleCat.subsingleton_of_isZero h
  exact Module.length_eq_zero

private lemma intLength_homology_euler (R : Type u) [Ring R]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} R) c)
    (σ : ι ≃ ι) (hσ : ∀ i, c.Rel i (σ i))
    (χ : ι → ℤ) (hχ : ∀ i, χ (σ i) = -χ i)
    (hf : ∀ i, Module.length R (K.X i) ≠ ⊤)
    (t : Finset ι) (ht : ∀ i ∉ t, IsZero (K.X i)) :
    (∑ᶠ i, χ i * ((Module.length R (K.X i)).toNat : ℤ)) =
      ∑ᶠ i, χ i * ((Module.length R (K.homology i)).toNat : ℤ) := by
  classical
  let B : ι → ℤ := fun i => χ i *
    ((Module.length R (LinearMap.range (K.d i (σ i)).hom)).toNat : ℤ)
  have hB : (Function.support B).Finite := by
    apply t.finite_toSet.subset
    intro i hi
    by_contra hit
    have hz : K.d i (σ i) = 0 := (ht i hit).eq_of_src _ _
    change χ i * ((Module.length R (LinearMap.range (K.d i (σ i)).hom)).toNat : ℤ) ≠ 0 at hi
    rw [hz] at hi
    have hzero : Subsingleton (LinearMap.range
        (0 : K.X i ⟶ K.X (σ i)).hom) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      obtain ⟨a', ha⟩ := a.2
      obtain ⟨b', hb⟩ := b.2
      exact ha.symm.trans hb
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero,
      mul_zero, ne_eq, not_true_eq_false] at hi
  have hH : (Function.support (fun i => χ i *
      ((Module.length R (K.homology i)).toNat : ℤ))).Finite := by
    apply t.finite_toSet.subset
    intro i hi
    by_contra hit
    have hz : IsZero (K.homology i) :=
      (K.sc i).isZero_homology_of_isZero_X₂ (ht i hit)
    simp [length_eq_zero_of_isZero R hz] at hi
  apply finsum_eq_of_add_sub_equiv _ _ B σ.symm hH hB
  intro i
  have he := intLength_shortComplex R (K.sc i) (hf i)
  have hp : c.prev i = σ.symm i := c.prev_eq' (by simpa using hσ (σ.symm i))
  have hn : c.next i = σ i := c.next_eq' (hσ i)
  change ((Module.length R (K.X i)).toNat : ℤ) =
    ((Module.length R (K.homology i)).toNat : ℤ) +
      ((Module.length R (LinearMap.range (K.d (c.prev i) i).hom)).toNat : ℤ) +
      ((Module.length R (LinearMap.range (K.d i (c.next i)).hom)).toNat : ℤ) at he
  rw [hp, hn] at he
  have hc : χ i = -χ (σ.symm i) := by simpa using hχ (σ.symm i)
  dsimp only [B]
  rw [σ.apply_symm_apply, he, hc]
  ring
private lemma intLength_spectralSequence_page_succ (R : Type u) [Ring R]
    (E : E₂CohomologicalSpectralSequence (ModuleCat.{v} R)) (r : ℤ) (hr : 2 ≤ r)
    (hf : ∀ i, Module.length R ((E.page r hr).X i) ≠ ⊤)
    (t : Finset (ℤ × ℤ)) (ht : ∀ i ∉ t, IsZero ((E.page r hr).X i)) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R ((E.page r hr).X i)).toNat : ℤ)) =
    ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R ((E.page (r + 1) (by omega)).X i)).toNat : ℤ) := by
  let σ : (ℤ × ℤ) ≃ (ℤ × ℤ) := Equiv.addRight (r, 1 - r)
  have he := intLength_homology_euler R (E.page r hr) σ (fun _ => rfl)
    (fun i => ((i.1 + i.2).negOnePow : ℤ)) (by
      intro i
      change (((i.1 + r) + (i.2 + (1 - r))).negOnePow : ℤ) = _
      rw [show (i.1 + r) + (i.2 + (1 - r)) = i.1 + i.2 + 1 by omega, Int.negOnePow_succ,
        Units.val_neg]) hf t ht
  refine he.trans (finsum_congr fun i => ?_)
  rw [(E.iso r (r + 1) i rfl hr).toLinearEquiv.length_eq]

private lemma length_homology_le (R : Type u) [Ring R]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} R) c)
    (i : ι) : Module.length R (K.homology i) ≤ Module.length R (K.X i) := by
  change Module.length R (K.sc i).homology ≤ Module.length R (K.sc i).X₂
  rw [length_shortComplex R (K.sc i)]
  exact le_trans le_self_add le_self_add

private lemma spectralSequence_page_length_ne_top (R : Type u) [Ring R]
    (E : E₂CohomologicalSpectralSequence (ModuleCat.{v} R))
    (hf : ∀ i, Module.length R ((E.page 2).X i) ≠ ⊤)
    (r : ℤ) (hr : 2 ≤ r) (i : ℤ × ℤ) :
    Module.length R ((E.page r hr).X i) ≠ ⊤ := by
  induction r, hr using Int.leInduction with
  | base => exact hf i
  | succ r hr ih =>
    rw [← (E.iso r (r + 1) i rfl hr).toLinearEquiv.length_eq]
    exact ne_of_lt (lt_of_le_of_lt (length_homology_le R (E.page r hr) i) ih.lt_top)

private lemma spectralSequence_page_isZero (R : Type u) [Ring R]
    (E : E₂CohomologicalSpectralSequence (ModuleCat.{v} R))
    (i : ℤ × ℤ) (hi : IsZero ((E.page 2).X i))
    (r : ℤ) (hr : 2 ≤ r) : IsZero ((E.page r hr).X i) := by
  induction r, hr using Int.leInduction with
  | base => exact hi
  | succ r hr ih =>
    exact IsZero.of_iso ((E.page r hr).sc i |>.isZero_homology_of_isZero_X₂ ih)
      (E.iso r (r + 1) i rfl hr).symm

private lemma intLength_spectralSequence_pages (R : Type u) [Ring R]
    (E : E₂CohomologicalSpectralSequence (ModuleCat.{v} R))
    (hf : ∀ i, Module.length R ((E.page 2).X i) ≠ ⊤)
    (t : Finset (ℤ × ℤ)) (ht : ∀ i ∉ t, IsZero ((E.page 2).X i))
    (r : ℤ) (hr : 2 ≤ r) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R ((E.page 2).X i)).toNat : ℤ)) =
    ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R ((E.page r hr).X i)).toNat : ℤ) := by
  induction r, hr using Int.leInduction with
  | base => rfl
  | succ r hr ih =>
    exact ih.trans (intLength_spectralSequence_page_succ R E r hr
      (spectralSequence_page_length_ne_top R E hf r hr) t
      (fun i hi => spectralSequence_page_isZero R E i (ht i hi) r hr))
private lemma length_eq_add_cokernel (R : Type u) [Ring R]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) [Mono f] :
    Module.length R N = Module.length R M + Module.length R ↑(cokernel f) := by
  have hs : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := inferInstanceAs (Mono f) }
  exact Module.length_eq_add_of_exact f.hom (cokernel.π f).hom
    hs.moduleCat_injective_f hs.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs.exact)

private lemma length_eq_sum_cokernel_of_isZero (R : Type u) [Ring R]
    (F : ℕ → ModuleCat.{v} R) (f : ∀ i, F (i + 1) ⟶ F i)
    [∀ i, Mono (f i)] (n : ℕ) (hn : IsZero (F n)) :
    Module.length R (F 0) = ∑ i ∈ Finset.range n, Module.length R ↑(cokernel (f i)) := by
  have he : ∀ m, Module.length R (F 0) =
      (∑ i ∈ Finset.range m, Module.length R ↑(cokernel (f i))) +
        Module.length R (F m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, length_eq_add_cokernel R (f m)]
      ac_rfl
  have : Subsingleton (F n) := ModuleCat.subsingleton_of_isZero hn
  simpa only [Module.length_eq_zero, add_zero] using he n
private lemma intLength_eq_sum_cokernel_of_isZero (R : Type u) [Ring R]
    (F : ℕ → ModuleCat.{v} R) (f : ∀ i, F (i + 1) ⟶ F i)
    [∀ i, Mono (f i)] (n : ℕ) (hn : IsZero (F n))
    (hfinite : Module.length R (F 0) ≠ ⊤) :
    ((Module.length R (F 0)).toNat : ℤ) =
      ∑ i ∈ Finset.range n, ((Module.length R ↑(cokernel (f i))).toNat : ℤ) := by
  have he := length_eq_sum_cokernel_of_isZero R F f n hn
  have hfi : ∀ i ∈ Finset.range n, Module.length R ↑(cokernel (f i)) ≠ ⊤ := by
    intro i hi
    apply ne_of_lt
    calc
      Module.length R ↑(cokernel (f i)) ≤
          ∑ j ∈ Finset.range n, Module.length R ↑(cokernel (f j)) :=
        Finset.single_le_sum (f := fun j => Module.length R ↑(cokernel (f j)))
          (fun _ _ => bot_le) hi
      _ < ⊤ := by rw [← he]; exact hfinite.lt_top
  rw [he, ENat.toNat_sum hfi, Nat.cast_sum]

open CochainComplex.DerivedTensorSpectralSequence

private lemma inducedHomologyFiltration_iso_of_eq_top
    {C : Type*} [Category C] [Abelian C]
    (T : CochainComplex C ℤ) (F : ∀ _p n : ℤ, Subobject (T.X n))
    (p n : ℤ) (h : F p n = ⊤) :
    Nonempty ((inducedHomologyFiltration T F p n : C) ≅ T.homology n) := by
  have he : inducedHomologyFiltration T F p n = ⊤ := by
    rw [inducedHomologyFiltration, h, Subobject.pullback_top, Subobject.exists_obj_top]
    exact Subobject.imageSubobject_eq_top_of_epi _
  rw [he]
  exact ⟨asIso (⊤ : Subobject (T.homology n)).arrow⟩

private lemma inducedHomologyFiltration_isZero_of_eq_bot
    {C : Type*} [Category C] [Abelian C]
    (T : CochainComplex C ℤ) (F : ∀ _p n : ℤ, Subobject (T.X n))
    (p n : ℤ) (h : F p n = ⊥) :
    IsZero (inducedHomologyFiltration T F p n : C) := by
  dsimp only [inducedHomologyFiltration]
  rw [h, Subobject.pullback_bot, Subobject.kernelSubobject_eq_bot_of_mono]
  apply IsZero.of_iso _ (Subobject.existsIsoImage _ _)
  rw [Subobject.bot_arrow, zero_comp]
  exact (isZero_zero C).of_iso imageZero

private lemma cokernel_ofLE_eq_inducedHomologyGradedPiece
    {C : Type*} [Category C] [Abelian C]
    (T : CochainComplex C ℤ) (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n) (p q n : ℤ) (hq : q = p + 1)
    (hle : inducedHomologyFiltration T F q n ≤ inducedHomologyFiltration T F p n) :
    cokernel (Subobject.ofLE _ _ hle) = inducedHomologyGradedPiece T F hF p n := by
  subst hq
  rfl

private lemma length_homology_eq_sum_graded (R : Type u) [Ring R]
    (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n)
    (a n : ℤ) (b : ℕ) (ha : F a n = ⊤) (hb : F (a + b) n = ⊥) :
    Module.length R (T.homology n) =
      ∑ i ∈ Finset.range b,
        Module.length R (↑(inducedHomologyGradedPiece T F hF (a + i) n)) := by
  let G : ℕ → ModuleCat.{v} R := fun i => inducedHomologyFiltration T F (a + i) n
  let g : ∀ i, G (i + 1) ⟶ G i := fun i =>
    Subobject.ofLE _ _ ((Subobject.exists (T.homologyπ n)).monotone
      ((Subobject.pullback (T.iCycles n)).monotone (hF _ _ n (by omega))))
  have hmono : ∀ i, Mono (g i) := fun i => by
    dsimp only [g]
    exact mono_of_mono_fac (Subobject.ofLE_arrow _)
  obtain ⟨e⟩ := inducedHomologyFiltration_iso_of_eq_top T F a n ha
  have he := @length_eq_sum_cokernel_of_isZero R _ G g hmono b
    (inducedHomologyFiltration_isZero_of_eq_bot T F (a + b) n hb)
  have hzero : Module.length R (G 0) = Module.length R (T.homology n) := by
    have hg : G 0 = (inducedHomologyFiltration T F a n : ModuleCat R) := by
      dsimp only [G]
      rw [Nat.cast_zero, add_zero]
    rw [hg]
    exact e.toLinearEquiv.length_eq
  rw [hzero] at he
  refine he.trans (Finset.sum_congr rfl fun i hi => ?_)
  exact (eqToIso (cokernel_ofLE_eq_inducedHomologyGradedPiece T F hF
    (a + (i : ℤ)) (a + ((i + 1 : ℕ) : ℤ)) n (by push_cast; ring) _)).toLinearEquiv.length_eq

private lemma exists_length_homology_eq_sum_page (R : Type u) [Ring R]
    (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (E : AssociatedFiltrationSpectralSequence T F)
    (a n : ℤ) (b : ℕ) (ha : F a n = ⊤) (hb : F (a + b) n = ⊥) :
    ∃ r₀ : ℤ, 2 ≤ r₀ ∧ ∀ (r : ℤ) (hr : 2 ≤ r), r₀ ≤ r →
      Module.length R (T.homology n) =
        ∑ i ∈ Finset.range b,
          Module.length R ((E.spectralSequence.page r (by omega)).X
            (a + i, n - (a + i))) := by
  classical
  choose r₀ hr₀ hstable using E.abuts
  by_cases hbzero : b = 0
  · subst b
    refine ⟨2, le_rfl, fun r hr hrr => ?_⟩
    simpa using length_homology_eq_sum_graded R T F E.decreasing a n 0 ha hb
  · let rmax : ℤ := max 2 ((Finset.range b).sup'
      (by simpa using hbzero)
      (fun i => r₀ (a + i) (n - (a + i))))
    refine ⟨rmax, le_max_left _ _, fun r hr hrr => ?_⟩
    rw [length_homology_eq_sum_graded R T F E.decreasing a n b ha hb]
    apply Finset.sum_congr rfl
    intro i hi
    have hri : r₀ (a + i) (n - (a + i)) ≤ r :=
      le_trans (Finset.le_sup' (f := fun i => r₀ (a + (i : ℕ)) (n - (a + (i : ℕ)))) hi)
        ((le_max_right _ _).trans hrr)
    obtain ⟨_, _, f, _, _, hf, _⟩ := hstable (a + i) (n - (a + i)) r
      hr hri
    have := hf
    have he := (asIso f).toLinearEquiv.length_eq
    rw [show a + (i : ℤ) + (n - (a + i)) = n by omega] at he
    exact he

private lemma exists_spectralSequence_page_length_stable (R : Type u) [Ring R]
    (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (E : AssociatedFiltrationSpectralSequence T F)
    (t : Finset (ℤ × ℤ))
    (ht : ∀ i ∉ t, IsZero ((E.spectralSequence.page 2).X i)) :
    ∃ r : ℤ, ∃ hr : 2 ≤ r, ∀ s : ℤ, ∀ hs : 2 ≤ s, r ≤ s → ∀ i : ℤ × ℤ,
      Module.length R ((E.spectralSequence.page s hs).X i) =
        Module.length R ((E.spectralSequence.page r hr).X i) := by
  classical
  choose r₀ hr₀ hstable using E.abuts
  let r : ℤ := 2 + (t.sup fun i => (r₀ i.1 i.2).toNat : ℕ)
  have hr : 2 ≤ r := by dsimp [r]; omega
  refine ⟨r, hr, fun s hs hrs i => ?_⟩
  by_cases hi : i ∈ t
  · have hri : r₀ i.1 i.2 ≤ r := by
      have hb := Finset.le_sup (f := fun i : ℤ × ℤ => (r₀ i.1 i.2).toNat) hi
      dsimp only [r]
      omega
    obtain ⟨_, _, f, _, _, hf, _⟩ := hstable i.1 i.2 r hr hri
    obtain ⟨_, _, g, _, _, hg, _⟩ := hstable i.1 i.2 s hs (hri.trans hrs)
    have := hf
    have := hg
    exact (asIso g).toLinearEquiv.length_eq.symm.trans
      (asIso f).toLinearEquiv.length_eq
  · have hz := spectralSequence_page_isZero R E.spectralSequence i (ht i hi)
    rw [length_eq_zero_of_isZero R (hz s hs), length_eq_zero_of_isZero R (hz r hr)]

private lemma exists_filtration_bounds (R : Type u) [Ring R]
    (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (hF : ∀ p p' n, p ≤ p' → F p' n ≤ F p n)
    (n : ℤ) (hfinite : ∃ a b : ℤ, F a n = ⊤ ∧ F b n = ⊥)
    (t : Finset (ℤ × ℤ)) :
    ∃ a : ℤ, ∃ b : ℕ, F a n = ⊤ ∧ F (a + b) n = ⊥ ∧
      ∀ i ∈ t, a ≤ i.1 ∧ i.1 < a + b := by
  obtain ⟨a₀, b₀, ha₀, hb₀⟩ := hfinite
  let m : ℤ := (t.sup fun i => i.1.natAbs : ℕ)
  let a := min a₀ (-m)
  let b := (max b₀ (m + 1) - a).toNat
  have hab : a + b = max b₀ (m + 1) := by
    have : 0 ≤ m := by dsimp [m]; omega
    dsimp only [a, b]
    omega
  refine ⟨a, b, ?_, ?_, fun i hi => ?_⟩
  · exact top_unique (ha₀ ▸ hF a a₀ n (min_le_left _ _))
  · rw [hab]
    exact bot_unique ((hF b₀ _ n (le_max_left _ _)).trans hb₀.le)
  · have hm : (i.1.natAbs : ℤ) ≤ m := by
      dsimp only [m]
      exact Int.ofNat_le.mpr (Finset.le_sup (f := fun i : ℤ × ℤ => i.1.natAbs) hi)
    have h₁ : i.1 ≤ (i.1.natAbs : ℤ) := Int.le_natAbs
    have h₂ := @Int.le_natAbs (-i.1)
    simp only [Int.natAbs_neg] at h₂
    dsimp only [a]
    rw [hab]
    omega

private lemma length_homology_eq_sum_page_fiber (R : Type u) [Ring R]
    (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (E : AssociatedFiltrationSpectralSequence T F)
    (t : Finset (ℤ × ℤ))
    (ht : ∀ i ∉ t, IsZero ((E.spectralSequence.page 2).X i))
    (r : ℤ) (hr : 2 ≤ r)
    (hstable : ∀ s : ℤ, ∀ hs : 2 ≤ s, r ≤ s → ∀ i : ℤ × ℤ,
      Module.length R ((E.spectralSequence.page s hs).X i) =
        Module.length R ((E.spectralSequence.page r hr).X i))
    (n : ℤ) (hfinite : ∃ a b : ℤ, F a n = ⊤ ∧ F b n = ⊥) :
    Module.length R (T.homology n) =
      ∑ i ∈ t.filter (fun i => i.1 + i.2 = n),
        Module.length R ((E.spectralSequence.page r hr).X i) := by
  obtain ⟨a, b, ha, hb, htbound⟩ := exists_filtration_bounds R T F E.decreasing n hfinite t
  obtain ⟨s, hs, he⟩ := exists_length_homology_eq_sum_page R T F E a n b ha hb
  rw [he (max r s) (le_trans hr (le_max_left _ _)) (le_max_right _ _)]
  simp_rw [hstable (max r s) (le_trans hr (le_max_left _ _)) (le_max_left _ _)]
  apply Finset.sum_bij_ne_zero (fun (j : ℕ) _ _ => (a + j, n - (a + j)))
  · intro j hj hne
    apply Finset.mem_filter.mpr
    refine ⟨?_, by omega⟩
    by_contra hnot
    exact hne (length_eq_zero_of_isZero R
      (spectralSequence_page_isZero R E.spectralSequence _ (ht _ hnot) r hr))
  · intro j hj hne j' hj' hne' heq
    have := congrArg Prod.fst heq
    dsimp only [Prod.fst] at this
    omega
  · intro i hi hne
    obtain ⟨hit, hin⟩ := Finset.mem_filter.mp hi
    obtain ⟨hlo, hhi⟩ := htbound i hit
    have hcast : a + ((i.1 - a).toNat : ℤ) = i.1 := by omega
    have hpair : (a + ((i.1 - a).toNat : ℤ), n - (a + (i.1 - a).toNat)) = i := by
      apply Prod.ext <;> dsimp <;> omega
    refine ⟨(i.1 - a).toNat, Finset.mem_range.mpr (by omega), ?_, hpair⟩
    exact (congrArg (fun j : ℤ × ℤ =>
      Module.length R ((E.spectralSequence.page r hr).X j) ≠ 0) hpair).mpr hne
  · intro j hj hne
    rfl

private lemma sum_image_sum_filter_eq {ι : Type*} {β : Type*} [AddCommMonoid β]
    (t : Finset ι) (g : ι → ℤ) (f : ι → β) :
    ∑ n ∈ t.image g, ∑ i ∈ t.filter (fun i => g i = n), f i = ∑ i ∈ t, f i := by
  classical
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨_, _, hi, _⟩ => hi, fun hi => ⟨g i, ⟨i, hi, rfl⟩, hi, rfl⟩⟩
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    exact fun i hia hib => hab (hia.2 ▸ hib.2 ▸ rfl)

private lemma intLength_spectralSequence_abutment (R : Type u) [Ring R]
    (T : CochainComplex (ModuleCat.{v} R) ℤ)
    (F : ∀ _p n : ℤ, Subobject (T.X n))
    (E : AssociatedFiltrationSpectralSequence T F)
    (hfinite : ∀ n, ∃ a b : ℤ, F a n = ⊤ ∧ F b n = ⊥)
    (hf : ∀ i, Module.length R ((E.spectralSequence.page 2).X i) ≠ ⊤)
    (t : Finset (ℤ × ℤ))
    (ht : ∀ i ∉ t, IsZero ((E.spectralSequence.page 2).X i)) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R ((E.spectralSequence.page 2).X i)).toNat : ℤ)) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * ((Module.length R (T.homology n)).toNat : ℤ) := by
  classical
  obtain ⟨r, hr, hstable⟩ := exists_spectralSequence_page_length_stable R T F E t ht
  have hlen := length_homology_eq_sum_page_fiber R T F E t ht r hr hstable
  have hf' := spectralSequence_page_length_ne_top R E.spectralSequence hf r hr
  have hzero : ∀ i ∉ t, Module.length R ((E.spectralSequence.page r hr).X i) = 0 := by
    intro i hi
    exact length_eq_zero_of_isZero R
      (spectralSequence_page_isZero R E.spectralSequence i (ht i hi) r hr)
  rw [intLength_spectralSequence_pages R E.spectralSequence hf t ht r hr]
  rw [finsum_eq_sum_of_support_subset _ (s := t)
    (Function.support_subset_iff'.mpr fun i hit => by simp [hzero i hit])]
  rw [finsum_eq_sum_of_support_subset _ (s := t.image (fun i => i.1 + i.2)) (by
    intro n hn
    by_contra hnot
    have he : t.filter (fun i => i.1 + i.2 = n) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun i hit hin => hnot (Finset.mem_image.mpr ⟨i, hit, hin⟩)
    exact hn (by dsimp only; rw [hlen n (hfinite n), he]; simp))]
  conv_rhs =>
    arg 2
    ext n
    rw [hlen n (hfinite n), ENat.toNat_sum (fun i _ => hf' i),
      Nat.cast_sum, Finset.mul_sum]
  symm
  apply (Finset.sum_congr rfl fun n hn => ?_).trans
    (sum_image_sum_filter_eq t (fun i : ℤ × ℤ => i.1 + i.2)
      (fun i : ℤ × ℤ => ((i.1 + i.2).negOnePow : ℤ) *
        ((Module.length R ((E.spectralSequence.page r hr).X i)).toNat : ℤ)))
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

section TensorFiltration

open CategoryTheory.MonoidalCategory

private lemma tensorSubobject_eq_top (R : Type u) [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (S : Subobject ((P ⊗ Q).X n))
    (hS : ∀ (i j : ℤ) (h : i + j = n),
      imageSubobject (HomologicalComplex.ιTensorObj P Q i j n h) ≤ S) : S = ⊤ := by
  have : Epi S.arrow := ⟨by
    intro A f g hfg
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    have hf : S.Factors (HomologicalComplex.ιTensorObj P Q i j n hij) :=
      Subobject.factors_of_le _ (hS i j hij)
        (by simpa only [Category.id_comp] using
          imageSubobject_factors_comp_self (HomologicalComplex.ιTensorObj P Q i j n hij) (𝟙 _))
    change HomologicalComplex.ιTensorObj P Q i j n hij ≫ f =
      HomologicalComplex.ιTensorObj P Q i j n hij ≫ g
    rw [← S.factorThru_arrow _ hf, Category.assoc, Category.assoc, hfg]⟩
  have : IsIso S.arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow S

/-- The summand of a tensor product of complexes indexed by `(i, j)` has image below any
subobject once `P` or `Q` vanishes in the corresponding degree. -/
private lemma imageSubobject_ιTensorObj_le_of_not_le (R : Type u) [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ] {i j n : ℤ} (hij : i + j = n)
    (hb : ¬(i ≤ bP ∧ j ≤ bQ)) (S : Subobject ((P ⊗ Q).X n)) :
    imageSubobject (HomologicalComplex.ιTensorObj P Q i j n hij) ≤ S := by
  have hz : IsZero (P.X i ⊗ Q.X j) := by
    by_cases hi : bP < i
    · exact (MonoidalCategory.tensorRight (C := ModuleCat.{u} R) (Q.X j)).map_isZero
        (P.isZero_of_isStrictlyLE bP i hi)
    · exact (MonoidalCategory.tensorLeft (C := ModuleCat.{u} R) (P.X i)).map_isZero
        (Q.isZero_of_isStrictlyLE bQ j (by omega))
  rw [hz.eq_of_src (HomologicalComplex.ιTensorObj P Q i j n hij) 0]
  simp

private lemma firstDegreeFiltration_bounded (R : Type u) [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ] (n : ℤ) :
    ∃ a b : ℤ, firstDegreeFiltration P Q bP bQ a n = ⊤ ∧
      firstDegreeFiltration P Q bP bQ b n = ⊥ := by
  classical
  refine ⟨n - bQ, bP + 1, ?_, ?_⟩
  · apply tensorSubobject_eq_top R P Q n
    intro i j hij
    by_cases hb : i ≤ bP ∧ j ≤ bQ
    · have hj : j = n - i := by omega
      subst j
      unfold firstDegreeFiltration
      exact Finset.le_sup (s := Finset.Icc (max (n - bQ) (n - bQ)) bP)
        (f := fun k : ℤ => imageSubobject
          (HomologicalComplex.ιTensorObj P Q k (n - k) n (by omega)))
        (b := i) (by simp only [Finset.mem_Icc]; omega)
    · exact imageSubobject_ιTensorObj_le_of_not_le R P Q bP bQ hij hb _
  · unfold firstDegreeFiltration
    rw [Finset.Icc_eq_empty_of_lt (show bP < max (bP + 1) (n - bQ) by omega)]
    simp

private lemma secondDegreeFiltration_bounded (R : Type u) [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (bP bQ : ℤ) [P.IsStrictlyLE bP] [Q.IsStrictlyLE bQ] (n : ℤ) :
    ∃ a b : ℤ, secondDegreeFiltration P Q bP bQ a n = ⊤ ∧
      secondDegreeFiltration P Q bP bQ b n = ⊥ := by
  classical
  refine ⟨n - bP, bQ + 1, ?_, ?_⟩
  · apply tensorSubobject_eq_top R P Q n
    intro i j hij
    by_cases hb : i ≤ bP ∧ j ≤ bQ
    · have hi : i = n - j := by omega
      subst i
      unfold secondDegreeFiltration
      exact Finset.le_sup (s := Finset.Icc (max (n - bP) (n - bP)) bQ)
        (f := fun k : ℤ => imageSubobject
          (HomologicalComplex.ιTensorObj P Q (n - k) k n (by omega)))
        (b := j) (by simp only [Finset.mem_Icc]; omega)
    · exact imageSubobject_ιTensorObj_le_of_not_le R P Q bP bQ hij hb _
  · unfold secondDegreeFiltration
    rw [Finset.Icc_eq_empty_of_lt (show bQ < max (bQ + 1) (n - bP) by omega)]
    simp

attribute [local instance 100000] HasDerivedCategory.standard

private abbrev derivedTensorHomology (R : Type u) [CommRing R]
    (K L : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) : ModuleCat.{u} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj L)

/-- Transport of `intLength_spectralSequence_abutment` along isomorphisms of the `E₂`-page and
of the abutment. -/
private lemma intLength_spectralSequence_abutment_of_iso (R : Type u) [CommRing R]
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (F : ∀ _p n : ℤ, Subobject (T.X n))
    (E : AssociatedFiltrationSpectralSequence T F)
    (hfinite : ∀ n, ∃ a b : ℤ, F a n = ⊤ ∧ F b n = ⊥)
    (X : ℤ × ℤ → ModuleCat.{u} R) (H : ℤ → ModuleCat.{u} R)
    (eX : ∀ i, (E.spectralSequence.page 2).X i ≅ X i) (eH : ∀ n, T.homology n ≅ H n)
    (t : Finset (ℤ × ℤ)) (hf : ∀ i, Module.length R (X i) ≠ ⊤) (ht : ∀ i, i ∉ t → IsZero (X i)) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) * ((Module.length R (X i)).toNat : ℤ)) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * ((Module.length R (H n)).toNat : ℤ) := by
  simp_rw [← (eX _).toLinearEquiv.length_eq, ← (eH _).toLinearEquiv.length_eq]
  exact intLength_spectralSequence_abutment R T F E hfinite
    (fun i => by rw [(eX i).toLinearEquiv.length_eq]; exact hf i)
    t fun i hi => (ht i hi).of_iso (eX i)

-- Comparing the filtration and derived tensor models requires additional elaboration.
private lemma intLength_derivedTensor_spectralSequence_left (R : Type u) [CommRing R]
    (K L : DerivedCategory.Minus (ModuleCat.{u} R))
    (t : Finset (ℤ × ℤ))
    (hf : ∀ i : ℤ × ℤ, Module.length R (derivedTensorHomology R K.1
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj L.1)) i.1) ≠ ⊤)
    (ht : ∀ i : ℤ × ℤ, i ∉ t → IsZero (derivedTensorHomology R K.1
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj L.1)) i.1)) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R (derivedTensorHomology R K.1
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj L.1)) i.1)).toNat : ℤ)) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) *
        ((Module.length R (derivedTensorHomology R K.1 L.1 n)).toNat : ℤ) := by
  obtain ⟨P, Q, bP, bQ, hP, hPproj, hQ, hQproj, hPflat, hQflat, eK, eL,
    E, E', first, second, first', second', abutment, firstOrdinary, secondOrdinary,
    firstDerived, secondDerived, hcompat⟩ := exists_derived_tensor_spectral_sequences R K L
  have := hP
  have := hQ
  exact intLength_spectralSequence_abutment_of_iso R _ _ E
    (firstDegreeFiltration_bounded R P Q bP bQ) _ _ (fun i => firstDerived i.1 i.2)
    (fun n => abutment n) t hf ht

-- Comparing the filtration and derived tensor models requires additional elaboration.
private lemma intLength_derivedTensor_spectralSequence_right (R : Type u) [CommRing R]
    (K L : DerivedCategory.Minus (ModuleCat.{u} R))
    (t : Finset (ℤ × ℤ))
    (hf : ∀ i : ℤ × ℤ, Module.length R (derivedTensorHomology R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj K.1)) L.1 i.1) ≠ ⊤)
    (ht : ∀ i : ℤ × ℤ, i ∉ t → IsZero (derivedTensorHomology R
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj K.1)) L.1 i.1)) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R (derivedTensorHomology R
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj K.1)) L.1 i.1)).toNat : ℤ)) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) *
        ((Module.length R (derivedTensorHomology R K.1 L.1 n)).toNat : ℤ) := by
  obtain ⟨P, Q, bP, bQ, hP, hPproj, hQ, hQproj, hPflat, hQflat, eK, eL,
    E, E', first, second, first', second', abutment, firstOrdinary, secondOrdinary,
    firstDerived, secondDerived, hcompat⟩ := exists_derived_tensor_spectral_sequences R K L
  have := hP
  have := hQ
  exact intLength_spectralSequence_abutment_of_iso R _ _ E'
    (secondDegreeFiltration_bounded R P Q bP bQ) _ _ (fun i => secondDerived i.1 i.2)
    (fun n => abutment n) t hf ht

private lemma quasiIso_tensorRight_of_kFlat
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso ((MonoidalCategory.tensorRight
      (C := CochainComplex (ModuleCat.{u} R) ℤ) K).map f) := by
  have hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 (show QuasiIso f from inferInstance)
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK
    ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright K).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

private noncomputable def derivedTensor_single_homology_iso
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (i : ℤ) :
    derivedTensorHomology R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) i ≅
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) ⊗
        (ProjectiveResolution.of N).cochainComplex).homology i := by
  let P := ProjectiveResolution.of M
  let Q := ProjectiveResolution.of N
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  have hP : P.cochainComplex.KFlat := CochainComplex.KFlat.kFlat_of_flat P.cochainComplex 0
  have hQ : Q.cochainComplex.KFlat := CochainComplex.KFlat.kFlat_of_flat Q.cochainComplex 0
  let eM := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M ≪≫
    (asIso (DerivedCategory.Q.map P.π')).symm
  let eN := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N ≪≫
    (asIso (DerivedCategory.Q.map Q.π')).symm
  have : QuasiIso ((MonoidalCategory.tensorRight
      (C := CochainComplex (ModuleCat.{u} R) ℤ) Q.cochainComplex).map P.π') :=
    quasiIso_tensorRight_of_kFlat Q.cochainComplex hQ P.π'
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((T.tensor.mapIso eM).app _ ≪≫ (T.tensor.obj _).mapIso eN ≪≫
        T.comparison P.cochainComplex Q.cochainComplex hP hQ) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _ ≪≫
    isoOfQuasiIsoAt (MonoidalCategory.tensorRight
      (C := CochainComplex (ModuleCat.{u} R) ℤ) Q.cochainComplex |>.map P.π') i

private noncomputable def leftDerivedNatIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [HasProjectiveResolutions C] [Abelian D] {F G : C ⥤ D}
    [F.Additive] [G.Additive] (e : F ≅ G) (n : ℕ) :
    F.leftDerived n ≅ G.leftDerived n where
  hom := NatTrans.leftDerived e.hom n
  inv := NatTrans.leftDerived e.inv n
  hom_inv_id := by
    rw [← NatTrans.leftDerived_comp, e.hom_inv_id, NatTrans.leftDerived_id]
  inv_hom_id := by
    rw [← NatTrans.leftDerived_comp, e.inv_hom_id, NatTrans.leftDerived_id]

private noncomputable def derivedTensor_single_torIso
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (i : ℤ) :
    derivedTensorHomology R ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) (-i) ≅
      CochainComplex.Tor.TorInDegree R i M N := by
  refine derivedTensor_single_homology_iso R M N (-i) ≪≫ ?_
  by_cases hi : 0 ≤ i
  · let e : tensorLeft M ≅ (CochainComplex.Tor.moduleTensorBifunctor R).obj M :=
      NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext; rfl)
    let e' := (leftDerivedNatIso e i.toNat).app N
    simpa only [Int.toNat_of_nonneg hi, CochainComplex.Tor.TorInDegree, hi,
      dite_true, StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology,
      StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex,
      ProjectiveResolution.cochainComplex, ComplexShape.Embedding.extendFunctor_obj,
      tensorLeft, curriedTensor_obj_obj] using
      (StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologySingle₀Iso M N i.toNat ≪≫ e')
  · let Q := (ProjectiveResolution.of N).cochainComplex
    let F := (tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)
    have hz : IsZero ((F.obj Q).X (-i)) :=
      (tensorLeft M).map_isZero (Q.isZero_of_isStrictlyLE 0 (-i) (by omega))
    have hhom : IsZero ((F.obj Q).homology (-i)) :=
      ((F.obj Q).sc (-i)).isZero_homology_of_isZero_X₂ hz
    have ht : IsZero (CochainComplex.Tor.TorInDegree R i M N) := by
      simp only [CochainComplex.Tor.TorInDegree, hi, dite_false]
      exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    exact (HomologicalComplex.homologyFunctor _ _ (-i)).mapIso
        (TotalTensorComplex.SingleTensor.singleTensorIso M Q) ≪≫
      hhom.iso ht

private noncomputable def torInDegreeIso
    (R : Type u) [CommRing R] {M M' N N' : ModuleCat.{u} R}
    (eM : M ≅ M') (eN : N ≅ N') (p : ℤ) :
    CochainComplex.Tor.TorInDegree R p M N ≅
      CochainComplex.Tor.TorInDegree R p M' N' := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  exact (derivedTensor_single_torIso R M N p).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-p)).mapIso
      ((T.mapIso (S.mapIso eM)).app (S.obj N) ≪≫
        (T.obj (S.obj M')).mapIso (S.mapIso eN)) ≪≫
    derivedTensor_single_torIso R M' N' p

private abbrev singleDerivedModule (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M

private abbrev tensorDerivedModules (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) :=
  ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
    (singleDerivedModule R M)).obj (singleDerivedModule R N)

private noncomputable def derivedTensor_homology_torIso
    (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (i : ℤ) :
    derivedTensorHomology R (singleDerivedModule R M) (singleDerivedModule R N) i ≅
      CochainComplex.Tor.TorInDegree R (-i) M N := by
  simpa only [neg_neg] using derivedTensor_single_torIso R M N (-i)

private lemma isZero_torInDegree_of_isZero_right (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) (hN : IsZero N) (p : ℤ) :
    IsZero (CochainComplex.Tor.TorInDegree R p M N) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  let _ := T.commShift_right K
  let _ := T.exact_right K
  have hzero := (T.tensor.obj K).map_isZero
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map_isZero hN)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-p)).map_isZero hzero).of_iso
    (derivedTensor_single_torIso R M N p).symm

private lemma isZero_torInDegree_of_isZero_left (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) (hM : IsZero M) (p : ℤ) :
    IsZero (CochainComplex.Tor.TorInDegree R p M N) := by
  let e := (derivedTensor_single_torIso R M N p).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-p)).mapIso
      (CochainComplex.DerivedTensor.derivedTensorProductCommIso
        (singleDerivedModule R M) (singleDerivedModule R N)) ≪≫
    derivedTensor_single_torIso R N M p
  exact (isZero_torInDegree_of_isZero_right R N M hM p).of_iso e

private lemma tensorDerivedModules_isLE (R : Type u) [CommRing R]
    (M N : ModuleCat.{u} R) : (tensorDerivedModules R M N).IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine IsZero.of_iso ?_ (derivedTensor_homology_torIso R M N i)
  simp only [CochainComplex.Tor.TorInDegree, show ¬ 0 ≤ -i by omega, dite_false]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

private noncomputable def leftIteratedTorIso
    (R : Type u) [CommRing R] (M N P : ModuleCat.{u} R) (i : ℤ × ℤ) :
    derivedTensorHomology R (singleDerivedModule R M)
      (singleDerivedModule R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj
        (tensorDerivedModules R N P))) i.1 ≅
      CochainComplex.Tor.TorInDegree R (-i.1) M
        (CochainComplex.Tor.TorInDegree R (-i.2) N P) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.1).mapIso
      ((T.obj (singleDerivedModule R M)).mapIso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
          (derivedTensor_homology_torIso R N P i.2))) ≪≫
    derivedTensor_homology_torIso R M _ i.1

private noncomputable def rightIteratedTorIso
    (R : Type u) [CommRing R] (M N P : ModuleCat.{u} R) (i : ℤ × ℤ) :
    derivedTensorHomology R
      (singleDerivedModule R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.2).obj
        (tensorDerivedModules R M N))) (singleDerivedModule R P) i.1 ≅
      CochainComplex.Tor.TorInDegree R (-i.1)
        (CochainComplex.Tor.TorInDegree R (-i.2) M N) P := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i.1).mapIso
      ((T.mapIso ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (derivedTensor_homology_torIso R M N i.2))).app (singleDerivedModule R P)) ≪≫
    derivedTensor_homology_torIso R _ P i.1

private lemma intLength_iteratedTor_assoc (R : Type u) [CommRing R]
    (M N P : ModuleCat.{u} R) (t₁ t₂ : Finset (ℤ × ℤ))
    (hf₁ : ∀ i : ℤ × ℤ, Module.length R (CochainComplex.Tor.TorInDegree R (-i.1) M
      (CochainComplex.Tor.TorInDegree R (-i.2) N P)) ≠ ⊤)
    (hf₂ : ∀ i : ℤ × ℤ, Module.length R (CochainComplex.Tor.TorInDegree R (-i.1)
      (CochainComplex.Tor.TorInDegree R (-i.2) M N) P) ≠ ⊤)
    (ht₁ : ∀ i : ℤ × ℤ, i ∉ t₁ → IsZero (CochainComplex.Tor.TorInDegree R (-i.1) M
      (CochainComplex.Tor.TorInDegree R (-i.2) N P)))
    (ht₂ : ∀ i : ℤ × ℤ, i ∉ t₂ → IsZero (CochainComplex.Tor.TorInDegree R (-i.1)
      (CochainComplex.Tor.TorInDegree R (-i.2) M N) P)) :
    (∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R (CochainComplex.Tor.TorInDegree R (-i.1) M
        (CochainComplex.Tor.TorInDegree R (-i.2) N P))).toNat : ℤ)) =
    ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) *
      ((Module.length R (CochainComplex.Tor.TorInDegree R (-i.1)
        (CochainComplex.Tor.TorInDegree R (-i.2) M N) P)).toNat : ℤ) := by
  let K : DerivedCategory.Minus (ModuleCat.{u} R) :=
    ⟨singleDerivedModule R M, ⟨0, inferInstance⟩⟩
  let L : DerivedCategory.Minus (ModuleCat.{u} R) :=
    ⟨tensorDerivedModules R N P, ⟨0, tensorDerivedModules_isLE R N P⟩⟩
  let K' : DerivedCategory.Minus (ModuleCat.{u} R) :=
    ⟨tensorDerivedModules R M N, ⟨0, tensorDerivedModules_isLE R M N⟩⟩
  let L' : DerivedCategory.Minus (ModuleCat.{u} R) :=
    ⟨singleDerivedModule R P, ⟨0, inferInstance⟩⟩
  have hleft := intLength_derivedTensor_spectralSequence_left R K L t₁
    (fun i => by rw [(leftIteratedTorIso R M N P i).toLinearEquiv.length_eq]; exact hf₁ i)
    (fun i hi => (ht₁ i hi).of_iso (leftIteratedTorIso R M N P i))
  have hright := intLength_derivedTensor_spectralSequence_right R K' L' t₂
    (fun i => by rw [(rightIteratedTorIso R M N P i).toLinearEquiv.length_eq]; exact hf₂ i)
    (fun i hi => (ht₂ i hi).of_iso (rightIteratedTorIso R M N P i))
  dsimp only [K, L, K', L'] at hleft hright
  simp_rw [(leftIteratedTorIso R M N P _).toLinearEquiv.length_eq] at hleft
  simp_rw [(rightIteratedTorIso R M N P _).toLinearEquiv.length_eq] at hright
  rw [hleft, hright]
  obtain ⟨associator, -, -⟩ := CochainComplex.DerivedTensor.derivedTensorProduct_associator R
  apply finsum_congr
  intro n
  congr 2
  apply congrArg ENat.toNat
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
    (associator (singleDerivedModule R M) (singleDerivedModule R N)
      (singleDerivedModule R P))).toLinearEquiv.length_eq.symm

end TensorFiltration

end EulerCharacteristic

section IteratedTor

open CategoryTheory.Limits

attribute [local instance 100000] HasDerivedCategory.standard

/-- Tor in a negative integral degree is the zero module. -/
private lemma isZero_torInDegree_of_neg (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    (p : ℤ) (hp : p < 0) : IsZero (CochainComplex.Tor.TorInDegree R p M N) := by
  simp only [CochainComplex.Tor.TorInDegree, show ¬ (0 ≤ p) by omega, dite_false]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- Tor in nonnegative integral degree is Mathlib's `Tor`. -/
private def torInDegreeIsoTor (R : Type u) [CommRing R] (M N : ModuleCat.{u} R) (p : ℕ) :
    CochainComplex.Tor.TorInDegree R (p : ℤ) M N ≅ ((Tor (ModuleCat.{u} R) p).obj M).obj N := by
  have e : MonoidalCategory.tensorLeft M ≅ (CochainComplex.Tor.moduleTensorBifunctor R).obj M :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext; rfl)
  refine Iso.trans (eqToIso ?_) ((leftDerivedNatIso e p).app N).symm
  simp only [CochainComplex.Tor.TorInDegree, Int.natCast_nonneg, dite_true, Int.toNat_natCast]

private lemma length_torInDegree_natCast (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    (p : ℕ) :
    Module.length R (CochainComplex.Tor.TorInDegree R (p : ℤ) M N)
      = Module.length R (((Tor (ModuleCat.{u} R) p).obj M).obj N) :=
  (torInDegreeIsoTor R M N p).toLinearEquiv.length_eq

private lemma intLength_eq_zero_of_isZero (A : Type u) [CommRing A] {Z : ModuleCat.{u} A}
    (h : IsZero Z) : ((Module.length A Z).toNat : ℤ) = 0 := by
  rw [length_eq_zero_of_isZero A h]
  rfl

private lemma length_ne_top_of_isZero (A : Type u) [CommRing A] {Z : ModuleCat.{u} A}
    (h : IsZero Z) : Module.length A Z ≠ ⊤ := by
  rw [length_eq_zero_of_isZero A h]
  exact ENat.zero_ne_top

/-- The left-associated iterated `Tor` module, read in integral degrees, is the left-associated
iterated `Tor` module of Mathlib. -/
private def iteratedTorIsoLeft (A : Type u) [CommRing A] (M N P : ModuleCat.{u} A) (p q : ℕ) :
    CochainComplex.Tor.TorInDegree A (p : ℤ) M
        (CochainComplex.Tor.TorInDegree A (q : ℤ) N P) ≅
      ((Tor (ModuleCat.{u} A) p).obj M).obj (((Tor (ModuleCat.{u} A) q).obj N).obj P) :=
  (torInDegreeIso A (Iso.refl M) (torInDegreeIsoTor A N P q) (p : ℤ)).trans
    (torInDegreeIsoTor A M _ p)

/-- The right-associated iterated `Tor` module, read in integral degrees, is the
right-associated iterated `Tor` module of Mathlib. -/
private def iteratedTorIsoRight (A : Type u) [CommRing A] (M N P : ModuleCat.{u} A) (p q : ℕ) :
    CochainComplex.Tor.TorInDegree A (p : ℤ)
        (CochainComplex.Tor.TorInDegree A (q : ℤ) M N) P ≅
      ((Tor (ModuleCat.{u} A) p).obj (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P :=
  (torInDegreeIso A (torInDegreeIsoTor A M N q) (Iso.refl P) (p : ℤ)).trans
    (torInDegreeIsoTor A _ P p)

/-- Reindexing an alternating double sum from pairs of natural numbers to pairs of integers by
negation, when both families vanish outside the matching finite rectangles. -/
private lemma finsum_natPair_eq_finsum_intPair (n : ℕ) (fn : ℕ × ℕ → ℤ) (fz : ℤ × ℤ → ℤ)
    (hn : ∀ pq : ℕ × ℕ, pq ∉ Finset.range (n + 1) ×ˢ Finset.range (n + 1) → fn pq = 0)
    (hz : ∀ i : ℤ × ℤ, i ∉ Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0 → fz i = 0)
    (hmatch : ∀ p q : ℕ, fn (p, q) = fz (-(p : ℤ), -(q : ℤ))) :
    ∑ᶠ pq : ℕ × ℕ, fn pq = ∑ᶠ i : ℤ × ℤ, fz i := by
  classical
  rw [finsum_eq_sum_of_support_subset fn
      (s := Finset.range (n + 1) ×ˢ Finset.range (n + 1))
      (Function.support_subset_iff'.mpr hn),
    finsum_eq_sum_of_support_subset fz
      (s := Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0)
      (Function.support_subset_iff'.mpr hz)]
  refine Finset.sum_nbij' (fun pq => (-(pq.1 : ℤ), -(pq.2 : ℤ)))
    (fun i => ((-i.1).toNat, (-i.2).toNat)) ?_ ?_ ?_ ?_ ?_
  · intro pq hpq
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hpq ⊢
    omega
  · intro i hi
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro pq _
    exact Prod.ext (by simp) (by simp)
  · intro i hi
    simp only [Finset.mem_product, Finset.mem_Icc] at hi
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · intro pq _
    exact hmatch pq.1 pq.2

/-- An integer pair is either the negative of a pair of natural numbers, or has a negative
coordinate after negation. -/
private lemma exists_natCast_or_neg (i : ℤ × ℤ) :
    (∃ p q : ℕ, -i.1 = p ∧ -i.2 = q) ∨ -i.1 < 0 ∨ -i.2 < 0 := by
  by_cases h1 : -i.1 < 0
  · exact Or.inr (Or.inl h1)
  by_cases h2 : -i.2 < 0
  · exact Or.inr (Or.inr h2)
  exact Or.inl ⟨(-i.1).toNat, (-i.2).toNat, by omega, by omega⟩

/-- Off the rectangle `[0, n] × [0, n]` the left-associated iterated `Tor` module in integral
degrees is zero: in a negative degree by definition, and above `n` by hypothesis. -/
private lemma isZero_iteratedTorInDegree_left (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ)
    (hvanL : ∀ p q : ℕ, n < p ∨ n < q →
      IsZero (((Tor (ModuleCat.{u} A) p).obj M).obj
        (((Tor (ModuleCat.{u} A) q).obj N).obj P)))
    (i : ℤ × ℤ) (hi : i ∉ Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0) :
    IsZero (CochainComplex.Tor.TorInDegree A (-i.1) M
      (CochainComplex.Tor.TorInDegree A (-i.2) N P)) := by
  simp only [Finset.mem_product, Finset.mem_Icc] at hi
  rcases exists_natCast_or_neg i with ⟨p, q, hp, hq⟩ | h | h
  · have hpq : n < p ∨ n < q := by omega
    rw [hp, hq]
    exact (hvanL p q hpq).of_iso (iteratedTorIsoLeft A M N P p q)
  · exact isZero_torInDegree_of_neg A M _ (-i.1) h
  · exact isZero_torInDegree_of_isZero_right A M _
      (isZero_torInDegree_of_neg A N P (-i.2) h) (-i.1)

/-- Off the rectangle `[0, n] × [0, n]` the right-associated iterated `Tor` module in integral
degrees is zero. -/
private lemma isZero_iteratedTorInDegree_right (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ)
    (hvanR : ∀ p q : ℕ, n < p ∨ n < q →
      IsZero (((Tor (ModuleCat.{u} A) p).obj
        (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P))
    (i : ℤ × ℤ) (hi : i ∉ Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0) :
    IsZero (CochainComplex.Tor.TorInDegree A (-i.1)
      (CochainComplex.Tor.TorInDegree A (-i.2) M N) P) := by
  simp only [Finset.mem_product, Finset.mem_Icc] at hi
  rcases exists_natCast_or_neg i with ⟨p, q, hp, hq⟩ | h | h
  · have hpq : n < p ∨ n < q := by omega
    rw [hp, hq]
    exact (hvanR p q hpq).of_iso (iteratedTorIsoRight A M N P p q)
  · exact isZero_torInDegree_of_neg A _ P (-i.1) h
  · exact isZero_torInDegree_of_isZero_left A _ P
      (isZero_torInDegree_of_neg A M N (-i.2) h) (-i.1)

/-- The left-associated iterated `Tor` module in integral degrees has finite length whenever the
corresponding iterated `Tor` modules of Mathlib do. -/
private lemma length_iteratedTorInDegree_left_ne_top (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A)
    (hfinL : ∀ p q : ℕ, Module.length A
      (((Tor (ModuleCat.{u} A) p).obj M).obj
        (((Tor (ModuleCat.{u} A) q).obj N).obj P)) ≠ ⊤)
    (i : ℤ × ℤ) :
    Module.length A (CochainComplex.Tor.TorInDegree A (-i.1) M
      (CochainComplex.Tor.TorInDegree A (-i.2) N P)) ≠ ⊤ := by
  rcases exists_natCast_or_neg i with ⟨p, q, hp, hq⟩ | h | h
  · rw [hp, hq, (iteratedTorIsoLeft A M N P p q).toLinearEquiv.length_eq]
    exact hfinL p q
  · exact length_ne_top_of_isZero A (isZero_torInDegree_of_neg A M _ (-i.1) h)
  · exact length_ne_top_of_isZero A (isZero_torInDegree_of_isZero_right A M _
      (isZero_torInDegree_of_neg A N P (-i.2) h) (-i.1))

/-- The right-associated iterated `Tor` module in integral degrees has finite length whenever
the corresponding iterated `Tor` modules of Mathlib do. -/
private lemma length_iteratedTorInDegree_right_ne_top (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A)
    (hfinR : ∀ p q : ℕ, Module.length A
      (((Tor (ModuleCat.{u} A) p).obj
        (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P) ≠ ⊤)
    (i : ℤ × ℤ) :
    Module.length A (CochainComplex.Tor.TorInDegree A (-i.1)
      (CochainComplex.Tor.TorInDegree A (-i.2) M N) P) ≠ ⊤ := by
  rcases exists_natCast_or_neg i with ⟨p, q, hp, hq⟩ | h | h
  · rw [hp, hq, (iteratedTorIsoRight A M N P p q).toLinearEquiv.length_eq]
    exact hfinR p q
  · exact length_ne_top_of_isZero A (isZero_torInDegree_of_neg A _ P (-i.1) h)
  · exact length_ne_top_of_isZero A (isZero_torInDegree_of_isZero_left A _ P
      (isZero_torInDegree_of_neg A M N (-i.2) h) (-i.1))

/-- Reindexing an alternating double sum of lengths from natural to integral degrees by negation,
for families vanishing off the matching finite rectangles. -/
private lemma finsum_alternating_length_natPair_eq_intPair (A : Type u) [CommRing A] (n : ℕ)
    (X : ℕ × ℕ → ModuleCat.{u} A) (Y : ℤ × ℤ → ModuleCat.{u} A)
    (hX : ∀ p q : ℕ, n < p ∨ n < q → IsZero (X (p, q)))
    (hY : ∀ i : ℤ × ℤ, i ∉ Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0 → IsZero (Y i))
    (hXY : ∀ p q : ℕ, Module.length A (Y (-(p : ℤ), -(q : ℤ))) = Module.length A (X (p, q))) :
    (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A (X pq)).toNat : ℤ))
      = ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) * ((Module.length A (Y i)).toNat : ℤ) := by
  refine finsum_natPair_eq_finsum_intPair n _ _ ?_ ?_ ?_
  · intro pq hpq
    simp only [Finset.mem_product, Finset.mem_range, not_and, not_lt] at hpq
    rw [intLength_eq_zero_of_isZero A (hX pq.1 pq.2 (by omega)), mul_zero]
  · intro i hi
    rw [intLength_eq_zero_of_isZero A (hY i hi), mul_zero]
  · intro p q
    have hs : ((-(p : ℤ)) + (-(q : ℤ))).negOnePow = ((p + q : ℕ) : ℤ).negOnePow := by
      rw [show (-(p : ℤ)) + (-(q : ℤ)) = -(((p + q : ℕ) : ℤ)) by push_cast; ring,
        Int.negOnePow_neg]
    change (-1 : ℤ) ^ (p + q) * _ = ((((-(p : ℤ)) + (-(q : ℤ))).negOnePow : ℤ)) * _
    rw [hs, Int.coe_negOnePow_natCast, hXY]

/-- Both alternating double sums of lengths of iterated `Tor` modules agree with the
corresponding sum in integral degrees. -/
private lemma finsum_alternating_length_tor_eq_left (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ)
    (hvanL : ∀ p q : ℕ, n < p ∨ n < q →
      IsZero (((Tor (ModuleCat.{u} A) p).obj M).obj
        (((Tor (ModuleCat.{u} A) q).obj N).obj P))) :
    (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj M).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj N).obj P))).toNat : ℤ))
      = ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) * ((Module.length A
        (CochainComplex.Tor.TorInDegree A (-i.1) M
          (CochainComplex.Tor.TorInDegree A (-i.2) N P))).toNat : ℤ) :=
  finsum_alternating_length_natPair_eq_intPair A n _ _ hvanL
    (isZero_iteratedTorInDegree_left A M N P n hvanL) fun p q => by
      rw [neg_neg, neg_neg]
      exact (iteratedTorIsoLeft A M N P p q).toLinearEquiv.length_eq

/-- The right-associated companion of `finsum_alternating_length_tor_eq_left`. -/
private lemma finsum_alternating_length_tor_eq_right (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ)
    (hvanR : ∀ p q : ℕ, n < p ∨ n < q →
      IsZero (((Tor (ModuleCat.{u} A) p).obj
        (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P)) :
    (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj M).obj N)).obj P)).toNat : ℤ))
      = ∑ᶠ i : ℤ × ℤ, ((i.1 + i.2).negOnePow : ℤ) * ((Module.length A
        (CochainComplex.Tor.TorInDegree A (-i.1)
          (CochainComplex.Tor.TorInDegree A (-i.2) M N) P)).toNat : ℤ) :=
  finsum_alternating_length_natPair_eq_intPair A n _ _ hvanR
    (isZero_iteratedTorInDegree_right A M N P n hvanR) fun p q => by
      rw [neg_neg, neg_neg]
      exact (iteratedTorIsoRight A M N P p q).toLinearEquiv.length_eq

/-- **Associativity of the triple intersection product, in local form.** Let `A` be a
commutative ring and `M`, `N`, `P` be `A`-modules. If the iterated `Tor` modules have finite
length and
vanish in bidegrees above `n`, then the two alternating double sums

`∑ᵢⱼ (-1)ⁱ⁺ʲ length Torᵢᴬ(M, Torⱼᴬ(N, P))`  and  `∑ᵢⱼ (-1)ⁱ⁺ʲ length Torᵢᴬ(Torⱼᴬ(M, N), P)`

are equal. Both compute the Euler characteristic of `M ⊗ᴸ N ⊗ᴸ P`, because they are the
`E₂`-pages of the two spectral sequences of the derived tensor product, and length is additive
on short exact sequences. -/
theorem finsum_alternating_length_tor_assoc (A : Type u) [CommRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ)
    (hfinL : ∀ p q : ℕ, Module.length A
      (((Tor (ModuleCat.{u} A) p).obj M).obj
        (((Tor (ModuleCat.{u} A) q).obj N).obj P)) ≠ ⊤)
    (hfinR : ∀ p q : ℕ, Module.length A
      (((Tor (ModuleCat.{u} A) p).obj
        (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P) ≠ ⊤)
    (hvanL : ∀ p q : ℕ, n < p ∨ n < q →
      IsZero (((Tor (ModuleCat.{u} A) p).obj M).obj
        (((Tor (ModuleCat.{u} A) q).obj N).obj P)))
    (hvanR : ∀ p q : ℕ, n < p ∨ n < q →
      IsZero (((Tor (ModuleCat.{u} A) p).obj
        (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P)) :
    (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj M).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj N).obj P))).toNat : ℤ))
      = ∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj M).obj N)).obj P)).toNat : ℤ) := by
  rw [finsum_alternating_length_tor_eq_left A M N P n hvanL,
    finsum_alternating_length_tor_eq_right A M N P n hvanR]
  exact intLength_iteratedTor_assoc A M N P
    (Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0)
    (Finset.Icc (-(n : ℤ)) 0 ×ˢ Finset.Icc (-(n : ℤ)) 0)
    (length_iteratedTorInDegree_left_ne_top A M N P hfinL)
    (length_iteratedTorInDegree_right_ne_top A M N P hfinR)
    (isZero_iteratedTorInDegree_left A M N P n hvanL)
    (isZero_iteratedTorInDegree_right A M N P n hvanR)

/-- Over a regular local ring of dimension at most `n` the left-associated iterated `Tor`
modules vanish in bidegrees above `n`. -/
private lemma isZero_iteratedTor_left (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ) (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞))
    (p q : ℕ) (hpq : n < p ∨ n < q) :
    IsZero (((Tor (ModuleCat.{u} A) p).obj M).obj
      (((Tor (ModuleCat.{u} A) q).obj N).obj P)) := by
  rcases hpq with hp | hq
  · exact AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing M _ n p hdim hp
  · exact (isZero_torInDegree_of_isZero_right A M _
      (AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing N P n q hdim hq)
      (p : ℤ)).of_iso (torInDegreeIsoTor A M _ p).symm

/-- Over a regular local ring of dimension at most `n` the right-associated iterated `Tor`
modules vanish in bidegrees above `n`. -/
private lemma isZero_iteratedTor_right (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (M N P : ModuleCat.{u} A) (n : ℕ) (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞))
    (p q : ℕ) (hpq : n < p ∨ n < q) :
    IsZero (((Tor (ModuleCat.{u} A) p).obj
      (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P) := by
  rcases hpq with hp | hq
  · exact AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing _ P n p hdim hp
  · exact (isZero_torInDegree_of_isZero_left A _ P
      (AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing M N n q hdim hq)
      (p : ℤ)).of_iso (torInDegreeIsoTor A _ P p).symm

/-- A finite module over a Noetherian local ring supported in the closed point has finite
length. -/
private lemma length_ne_top_of_support_subset_closedPoint {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (X : Type u) [AddCommGroup X] [Module A X]
    [Module.Finite A X] (hX : Module.support A X ⊆ {IsLocalRing.closedPoint A}) :
    Module.length A X ≠ ⊤ := by
  rw [Module.length_ne_top_iff]
  cases subsingleton_or_nontrivial X with
  | inl _ => exact IsFiniteLength.of_subsingleton
  | inr _ =>
    exact isFiniteLength_of_support (hX.antisymm
      (Set.singleton_subset_iff.mpr (IsLocalRing.closedPoint_mem_support A X)))

/-- If the supports of three finite modules over a Noetherian local ring meet only in the
closed point, then every left-associated iterated `Tor` module has finite length: it is a
finite module whose support lies in all three supports. -/
private lemma length_iteratedTor_left_ne_top (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M N P : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N]
    [Module.Finite A P]
    (hsupp : Module.support A M ∩ Module.support A N ∩ Module.support A P ⊆
      {IsLocalRing.closedPoint A}) (p q : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) p).obj M).obj
      (((Tor (ModuleCat.{u} A) q).obj N).obj P)) ≠ ⊤ := by
  have hT : Module.Finite A (((Tor (ModuleCat.{u} A) q).obj N).obj P) :=
    tor_finite_of_noetherian A N P q
  have : Module.Finite A (((Tor (ModuleCat.{u} A) p).obj M).obj
      (((Tor (ModuleCat.{u} A) q).obj N).obj P)) :=
    tor_finite_of_noetherian A M (((Tor (ModuleCat.{u} A) q).obj N).obj P) p
  refine length_ne_top_of_support_subset_closedPoint _
    ((support_tor_subset_inter M (((Tor (ModuleCat.{u} A) q).obj N).obj P) p).trans ?_)
  rintro x ⟨hxM, hxT⟩
  obtain ⟨hxN, hxP⟩ := support_tor_subset_inter N P q hxT
  exact hsupp ⟨⟨hxM, hxN⟩, hxP⟩

/-- If the supports of three finite modules over a Noetherian local ring meet only in the
closed point, then every right-associated iterated `Tor` module has finite length. -/
private lemma length_iteratedTor_right_ne_top (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M N P : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N]
    [Module.Finite A P]
    (hsupp : Module.support A M ∩ Module.support A N ∩ Module.support A P ⊆
      {IsLocalRing.closedPoint A}) (p q : ℕ) :
    Module.length A (((Tor (ModuleCat.{u} A) p).obj
      (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P) ≠ ⊤ := by
  have hT : Module.Finite A (((Tor (ModuleCat.{u} A) q).obj M).obj N) :=
    tor_finite_of_noetherian A M N q
  have : Module.Finite A (((Tor (ModuleCat.{u} A) p).obj
      (((Tor (ModuleCat.{u} A) q).obj M).obj N)).obj P) :=
    tor_finite_of_noetherian A (((Tor (ModuleCat.{u} A) q).obj M).obj N) P p
  refine length_ne_top_of_support_subset_closedPoint _
    ((support_tor_subset_inter (((Tor (ModuleCat.{u} A) q).obj M).obj N) P p).trans ?_)
  rintro x ⟨hxT, hxP⟩
  obtain ⟨hxM, hxN⟩ := support_tor_subset_inter M N q hxT
  exact hsupp ⟨⟨hxM, hxN⟩, hxP⟩

/-- **Stacks 0B1L: associativity of intersections, at a point.** Let `A` be a regular local ring
of dimension at most `n` — the local ring of a nonsingular variety `X` at the generic point of a
component `Z` of `U ∩ V ∩ W` — and let `M`, `N`, `P` be finite `A`-modules whose supports meet
only in the maximal ideal, which is what it means for `Z` to be isolated in `U ∩ V ∩ W`. Then

`∑ᵢⱼ (-1)ⁱ⁺ʲ length Torᵢᴬ(M, Torⱼᴬ(N, P)) = ∑ᵢⱼ (-1)ⁱ⁺ʲ length Torᵢᴬ(Torⱼᴬ(M, N), P)`,

both sums being finite. For `M`, `N`, `P` the local rings of `U`, `V`, `W` the two sides are the
coefficients of `Z` in `U · (V · W)` and in `(U · V) · W`. -/
@[stacks 0B1L "the associativity `U · (V · W) = (U · V) · W` in local form at the local ring `A` \
of the ambient nonsingular variety at the generic point of a component of the triple \
intersection. By the Tor formula of Stacks 0B0W the coefficient of such a component in \
`U · (V · W)` is the alternating double sum `∑ᵢⱼ (-1)^(i+j) length_A Torᵢ^A(𝒪_U, Torⱼ^A(𝒪_V, \
𝒪_W))` and its coefficient in `(U · V) · W` is the right-associated sum; what is proved here is \
that those two sums agree, for arbitrary finite `A`-modules in place of the three local rings \
whose supports meet only in the maximal ideal. That support condition is the local form of the \
source's hypotheses that `U`, `V`, `W` meet properly pairwise and that \
`dim (U ∩ V ∩ W) ≤ dim U + dim V + dim W - 2 dim X`, which the source uses for exactly this \
purpose: to bound the dimensions of the supports of the sheaves appearing in the two sums. \
Every length in the two sums is then finite, since a `Tor` module of finite modules over a \
Noetherian ring is finite by Stacks 0AZ4 and its support lies in the intersection of the two \
supports, so each iterated `Tor` module is a finite module supported in the maximal ideal. The \
identity of the two sums is the claim the source's proof establishes, by the double-complex \
spectral sequence of Homology Section 012X in the form of More on Algebra Example 0662 \
(in the library as \
`CochainComplex.DerivedTensorSpectralSequence.exists_derived_tensor_spectral_sequences`) \
together with the additivity of length on short exact sequences."]
theorem finsum_alternating_length_tor_assoc_of_isRegularLocalRing (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (M N P : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N]
    [Module.Finite A P] (n : ℕ) (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞))
    (hsupp : Module.support A M ∩ Module.support A N ∩ Module.support A P ⊆
      {IsLocalRing.closedPoint A}) :
    (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj M).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj N).obj P))).toNat : ℤ))
      = ∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj M).obj N)).obj P)).toNat : ℤ) :=
  finsum_alternating_length_tor_assoc A M N P n
    (length_iteratedTor_left_ne_top A M N P hsupp)
    (length_iteratedTor_right_ne_top A M N P hsupp)
    (isZero_iteratedTor_left A M N P n hdim) (isZero_iteratedTor_right A M N P n hdim)

/-- **Stacks 0B1L for three closed subvarieties, at a point.** The case of the three local rings
`A ⧸ I`, `A ⧸ J`, `A ⧸ K` of closed subvarieties `U`, `V`, `W` cut out at the point by the
ideals `I`, `J`, `K`: the two iterated alternating sums of lengths of `Tor` modules agree. -/
@[stacks 0B1L "the associativity `U · (V · W) = (U · V) · W` in local form, for the three local \
rings `A ⧸ I`, `A ⧸ J`, `A ⧸ K` of the subvarieties at the generic point of a component of the \
triple intersection; the two sides are the coefficients of that component in the two iterated \
products, by the Tor formula of Stacks 0B0W. See \
`Stacks.Intersection.finsum_alternating_length_tor_assoc_of_isRegularLocalRing` for what is and \
is not carried."]
theorem finsum_alternating_length_tor_assoc_quotient (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (I J K : Ideal A) (n : ℕ)
    (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞))
    (hfinL : ∀ p q : ℕ, Module.length A
      (((Tor (ModuleCat.{u} A) p).obj (ModuleCat.of A (A ⧸ I))).obj
        (((Tor (ModuleCat.{u} A) q).obj (ModuleCat.of A (A ⧸ J))).obj
          (ModuleCat.of A (A ⧸ K)))) ≠ ⊤)
    (hfinR : ∀ p q : ℕ, Module.length A
      (((Tor (ModuleCat.{u} A) p).obj
        (((Tor (ModuleCat.{u} A) q).obj (ModuleCat.of A (A ⧸ I))).obj
          (ModuleCat.of A (A ⧸ J)))).obj (ModuleCat.of A (A ⧸ K))) ≠ ⊤) :
    (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj (ModuleCat.of A (A ⧸ I))).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj (ModuleCat.of A (A ⧸ J))).obj
            (ModuleCat.of A (A ⧸ K))))).toNat : ℤ))
      = ∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length A
        (((Tor (ModuleCat.{u} A) pq.1).obj
          (((Tor (ModuleCat.{u} A) pq.2).obj (ModuleCat.of A (A ⧸ I))).obj
            (ModuleCat.of A (A ⧸ J)))).obj (ModuleCat.of A (A ⧸ K)))).toNat : ℤ) :=
  finsum_alternating_length_tor_assoc A (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A (A ⧸ J))
    (ModuleCat.of A (A ⧸ K)) n hfinL hfinR
    (isZero_iteratedTor_left A (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A (A ⧸ J))
      (ModuleCat.of A (A ⧸ K)) n hdim)
    (isZero_iteratedTor_right A (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A (A ⧸ J))
      (ModuleCat.of A (A ⧸ K)) n hdim)

end IteratedTor

end Stacks.Intersection

end
