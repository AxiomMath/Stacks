module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Dimension of an algebra over a finite base from the dimensions of its fibres

Let `k` be a field, let `B` be a finite `k`-algebra and let `A` be a `B`-algebra. If for every
maximal ideal of `B` the fibre of `A` over it has dimension at most `n` over the corresponding
residue field, then `A` is a finite `k`-algebra of dimension at most `n` times the dimension
of `B`.

## Main results

* `Algebra.finite_and_finrank_le_of_finrank_fiber_le` bounds the dimension of `A` over `k` by the
  product of the fibre bound and the dimension of `B` over `k`.

## Implementation notes

A finite algebra over a field is Artinian, so the primes of `B` are its maximal ideals and the
bound on the fibres makes `A` quasi-finite, hence finite, over `B`. Nakayama's lemma, in the form
`TensorProduct.spanFinrank_top_eq_of_residueField`, turns the bound on the dimension of a fibre
into a generating family of that size for the localization of `A` at the corresponding maximal
ideal. The generating families at the several maximal ideals are then glued into one family of `n`
global generators, using the decomposition of an Artinian ring as the product of its localizations
to produce an idempotent-like family of scalars; a surjection from `B ^ n` onto `A` finally bounds
the dimension.

## References

* [Stacks Project, Tag 03J6](https://stacks.math.columbia.edu/tag/03J6)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

/-- The dimension of a module which is a quotient of `n` copies of a finite algebra is at
most `n` times the dimension of that algebra. -/
private lemma finrank_le_of_surjective_pi {k B A : Type u} [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup A] [Module B A] [Module k A] [IsScalarTower k B A] [Module.Finite k B]
    [Module.Finite k A] (n : ℕ) (f : (Fin n → B) →ₗ[B] A) (hf : Function.Surjective f) :
    Module.finrank k A ≤ n * Module.finrank k B := by
  simpa [Module.finrank_pi_fintype] using
    LinearMap.finrank_le_finrank_of_surjective (f := f.restrictScalars k) hf

/-- Generating families of `n` elements for all the localizations of a module at the maximal
ideals of an Artinian ring assemble into one global generating family of `n` elements. -/
private lemma exists_span_eq_top_of_localized {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [IsArtinianRing R] (n : ℕ)
    (h : ∀ m : MaximalSpectrum R, ∃ v : Fin n → M,
      Submodule.span (Localization.AtPrime m.asIdeal)
        (Set.range fun i ↦ LocalizedModule.mkLinearMap m.asIdeal.primeCompl M (v i)) = ⊤) :
    ∃ v : Fin n → M, Submodule.span R (Set.range v) = ⊤ := by
  classical
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  choose v hv using h
  let d (m : MaximalSpectrum R) : MaximalSpectrum.PiLocalization R :=
    fun j ↦ if j = m then 1 else 0
  let e (m : MaximalSpectrum R) : R := (MaximalSpectrum.toPiLocalizationEquiv R).symm (d m)
  have he (m j : MaximalSpectrum R) :
      algebraMap R (Localization.AtPrime j.asIdeal) (e m) = if j = m then 1 else 0 := by
    calc
      algebraMap R (Localization.AtPrime j.asIdeal) (e m) =
          MaximalSpectrum.toPiLocalizationEquiv R (e m) j := rfl
      _ = d m j := by
        simpa [e] using congrArg (fun x : MaximalSpectrum.PiLocalization R ↦ x j)
          ((MaximalSpectrum.toPiLocalizationEquiv R).apply_symm_apply (d m))
      _ = if j = m then 1 else 0 := by simp [d]
  let w (i : Fin n) : M := ∑ m : MaximalSpectrum R, e m • v m i
  refine ⟨w, ?_⟩
  apply Submodule.eq_top_of_localization_maximal
    (fun P _ ↦ Localization.AtPrime P) (fun P _ ↦ LocalizedModule P.primeCompl M)
    (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M)
    (N := Submodule.span R (Set.range w)) ?_
  intro j hj
  let m : MaximalSpectrum R := ⟨j, hj⟩
  rw [Submodule.localized'_span]
  have hwi (i : Fin n) :
      LocalizedModule.mkLinearMap j.primeCompl M (w i) =
        LocalizedModule.mkLinearMap j.primeCompl M (v m i) := by
    have hsmul (a : R) (z : LocalizedModule j.primeCompl M) :
        a • z = algebraMap R (Localization.AtPrime j) a • z :=
      (IsScalarTower.algebraMap_smul (A := Localization.AtPrime j) a z).symm
    have he' (x : MaximalSpectrum R) :
        algebraMap R (Localization.AtPrime j) (e x) = if m = x then 1 else 0 := by
      simpa [m] using he x m
    simp only [w, map_sum, map_smul, hsmul]
    rw [Finset.sum_eq_single m]
    · simp [he']
    · intro x _ hxm
      simp [he', hxm.symm]
    · simp
  refine eq_top_mono (Submodule.span_le.2 ?_) (hv m)
  rintro x ⟨i, rfl⟩
  change LocalizedModule.mkLinearMap j.primeCompl M (v m i) ∈ _
  rw [← hwi i]
  exact Submodule.subset_span ⟨w i, ⟨i, rfl⟩, rfl⟩

/-- A finite generating set of at most `n` elements, transported through a map, yields a family
indexed by `Fin n` whose image still spans. -/
private lemma exists_fin_of_span_image_eq_top {R M N : Type*} [Semiring R] [Zero M]
    [AddCommMonoid N] [Module R N] (n : ℕ) (f : M → N) (s : Set M) (hs : s.Finite)
    (hcard : s.ncard ≤ n) (hspan : Submodule.span R (f '' s) = ⊤) :
    ∃ v : Fin n → M, Submodule.span R (Set.range (f ∘ v)) = ⊤ := by
  classical
  let T := {x // x ∈ s}
  have : Finite T := hs.to_subtype
  let : Fintype T := Fintype.ofFinite T
  have hcard' : Fintype.card T ≤ Fintype.card (Fin n) := by
    simpa [T, Nat.card_eq_fintype_card] using hcard
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard'
  let v : Fin n → M := Function.extend (g : T → Fin n) (fun x ↦ (x : M)) 0
  have hvg (x : T) : v (g x) = x.1 := g.injective.extend_apply _ _ x
  refine ⟨v, eq_top_mono (Submodule.span_le.2 ?_) hspan⟩
  rintro x ⟨a, ha, rfl⟩
  exact Submodule.subset_span
    ⟨g ⟨a, ha⟩, by simpa [Function.comp_def] using congrArg f (hvg ⟨a, ha⟩)⟩

/-- If every localization of `A` at a maximal ideal of `B` is generated by `n` elements, then the
dimension of `A` over `k` is at most `n` times the dimension of `B`. -/
private lemma finrank_le_of_localized_span {k B A : Type u} [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup A] [Module B A] [Module k A] [IsScalarTower k B A] [IsArtinianRing B]
    [Module.Finite k B] [Module.Finite k A] (n : ℕ)
    (h : ∀ m : MaximalSpectrum B, ∃ v : Fin n → A,
      Submodule.span (Localization.AtPrime m.asIdeal)
        (Set.range fun i ↦ LocalizedModule.mkLinearMap m.asIdeal.primeCompl A (v i)) = ⊤) :
    Module.finrank k A ≤ n * Module.finrank k B := by
  obtain ⟨v, hv⟩ := exists_span_eq_top_of_localized n h
  exact finrank_le_of_surjective_pi n (Fintype.linearCombination B v)
    ((span_range_eq_top_iff_surjective_fintypeLinearCombination B v).mp hv)

/-- **Nakayama's lemma at a maximal ideal.** A bound on the dimension of the fibre of `A` at a
maximal ideal of `B` bounds the number of generators of the localization of `A` there. -/
private lemma exists_localized_span_of_finrank_fiber_le {B A : Type u} [CommRing B] [CommRing A]
    [Algebra B A] [Module.Finite B A] (n : ℕ) (m : MaximalSpectrum B)
    (hfiber : Module.finrank m.asIdeal.ResidueField (m.asIdeal.Fiber A) ≤ n) :
    ∃ v : Fin n → A,
      Submodule.span (Localization.AtPrime m.asIdeal)
        (Set.range fun i ↦ LocalizedModule.mkLinearMap m.asIdeal.primeCompl A (v i)) = ⊤ := by
  classical
  let R := Localization.AtPrime m.asIdeal
  let M := LocalizedModule m.asIdeal.primeCompl A
  let κ := m.asIdeal.ResidueField
  let eLoc : M ≃ₗ[R] R ⊗[B] A :=
    LocalizedModule.equivTensorProduct (R := B) m.asIdeal.primeCompl A
  let eFiber : κ ⊗[R] M ≃ₗ[κ] m.asIdeal.Fiber A :=
    (eLoc.baseChange R κ M (R ⊗[B] A)).trans
      (Algebra.TensorProduct.cancelBaseChange B R κ κ A).toLinearEquiv
  have hfg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
  have hspanFinrank : (⊤ : Submodule R M).spanFinrank ≤ n := by
    calc
      (⊤ : Submodule R M).spanFinrank =
          (⊤ : Submodule κ (κ ⊗[R] (⊤ : Submodule R M))).spanFinrank :=
        (TensorProduct.spanFinrank_top_eq_of_residueField (N := (⊤ : Submodule R M)) hfg).symm
      _ = Module.finrank κ (κ ⊗[R] (⊤ : Submodule R M)) :=
        Module.finrank_eq_spanFinrank_of_free.symm
      _ = Module.finrank κ (κ ⊗[R] M) :=
        (Submodule.topEquiv.baseChange R κ (⊤ : Submodule R M) M).finrank_eq
      _ ≤ n := eFiber.finrank_eq.trans_le hfiber
  obtain ⟨t, htcard, htspan⟩ := hfg.exists_span_finset_card_eq_spanFinrank
  let S := m.asIdeal.primeCompl
  let f : A →ₗ[B] M := LocalizedModule.mkLinearMap S A
  let num (x : M) : A := (Classical.choose (IsLocalizedModule.surj S f x)).1
  let den (x : M) : S := (Classical.choose (IsLocalizedModule.surj S f x)).2
  have hden (x : M) : (den x : B) • x = f (num x) :=
    Classical.choose_spec (IsLocalizedModule.surj S f x)
  let s : Finset A := t.image num
  have hmem (x : M) (hx : x ∈ t) : x ∈ Submodule.span R (f '' (s : Set A)) := by
    have hnum : f (num x) ∈ Submodule.span R (f '' (s : Set A)) :=
      Submodule.subset_span ⟨num x, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩), rfl⟩
    have hd := hden x
    rw [← algebraMap_smul R, ← Units.smul_isUnit (IsLocalization.map_units R (den x)),
      eq_comm, ← inv_smul_eq_iff] at hd
    exact hd ▸ Submodule.smul_mem _ _ hnum
  have hspan : Submodule.span R (f '' (s : Set A)) = ⊤ :=
    eq_top_mono (Submodule.span_le.2 fun x hx ↦ hmem x hx) htspan
  have hcard : (s : Set A).ncard ≤ n := by
    calc
      (s : Set A).ncard = s.card := by simp
      _ ≤ t.card := Finset.card_image_le
      _ = (⊤ : Submodule R M).spanFinrank := htcard
      _ ≤ n := hspanFinrank
  exact exists_fin_of_span_image_eq_top n f (s : Set A) s.finite_toSet hcard hspan

/-- If the fibres of a `B`-algebra `A` over the maximal ideals of a finite `k`-algebra `B` all
have dimension at most `n`, then `A` is a finite `k`-algebra of dimension at most `n` times the
dimension of `B`. -/
theorem finite_and_finrank_le_of_finrank_fiber_le {k B A : Type u} [Field k] [CommRing B]
    [CommRing A] [Algebra k B] [Algebra B A] [Algebra k A] [IsScalarTower k B A]
    [Module.Finite k B] (n : ℕ)
    (h : ∀ m : MaximalSpectrum B,
      Module.Finite m.asIdeal.ResidueField (m.asIdeal.Fiber A) ∧
        Module.finrank m.asIdeal.ResidueField (m.asIdeal.Fiber A) ≤ n) :
    Module.Finite k A ∧ Module.finrank k A ≤ n * Module.finrank k B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : Algebra.QuasiFinite B A :=
    ⟨fun P hP ↦ (h ⟨P, (IsArtinianRing.isPrime_iff_isMaximal P).mp hP⟩).1⟩
  have : Module.Finite B A := Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  have : Module.Finite k A := Module.Finite.trans B A
  exact ⟨inferInstance, finrank_le_of_localized_span n fun m ↦
    exists_localized_span_of_finrank_fiber_le n m (h m).2⟩

end Algebra

end
