module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.RingTheory.LocalCohomology.AnnihilatorPower
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthTwo
public import StacksFrontier.RingTheory.LocalCohomology.SupportedModulesAcyclic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of local cohomology and annihilators

Let `A` be a Noetherian ring, `T ⊆ Spec(A)` a subset stable under specialization, `M` a finite
`A`-module and `n ≥ 0`. The local cohomology modules `H^i_T(M)` are finite for `i ≤ n` exactly
when a single ideal `J` with `V(J) ⊆ T` annihilates all of them for `i ≤ n`.

The easy direction is formal: a finite module is annihilated by its own annihilator, and the zero
locus of the annihilator of a finite module is its support, which for `H^i_T(M)` is contained in
`T`; multiplying the finitely many annihilators for `0 ≤ i ≤ n` gives one ideal.

The substantial direction is Faltings' induction on `n`. One first replaces `M` by `M/Γ_T(M)`,
which has the same local cohomology in positive degrees because `Γ_T(M)` is acyclic for `Γ_T`, and
has no `T`-supported sections at all. No associated prime of such a module lies in `T`, so prime
avoidance produces an `f ∈ J` which is a nonzerodivisor on it. Multiplication by `f` acts as zero
on every `H^i_T` in the range, so the long exact sequence of `0 → M → M → M/fM → 0` breaks into
short exact sequences
`0 → H^i_T(M) → H^i_T(M/fM) → H^{i+1}_T(M) → 0` for `i ≤ n - 1`. Hence `J^2` annihilates
`H^i_T(M/fM)` for `i ≤ n - 1`, the inductive hypothesis makes those modules finite, and the same
short exact sequences then make `H^{i+1}_T(M)` finite.

## Main results

* `Stacks.LocalCohomology.sectionsWithSupportIn_quotient_eq_bot` — a module has no `T`-supported
  sections after dividing by its `T`-supported sections.
* `Stacks.LocalCohomology.isIso_localCohomologyMap_quotientSectionsWithSupportInπ` — the quotient
  map induces isomorphisms on local cohomology in positive degrees.
* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_exists_annihilator` —
  **Stacks 0AW8, equivalence of (1) and (2).**
* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator` — its
  form for closed support `V(I)`, where the annihilating ideal can be taken to be a power of `I`.

## Implementation notes

No `@[stacks]` attribute is placed here. Tag 0AW8 states the equivalence of three conditions; the
half proved here is `(1) ⇔ (2)`, and the complementary half `(2) ⇔ (3)` is
`Stacks.LocalCohomology.exists_annihilator_iff_exists_power_annihilator` in
`StacksFrontier/RingTheory/LocalCohomology/AnnihilatorPower.lean`, where a comment records why
no attribute was placed on half a covering set. Together the two now cover the lemma, so the
attribute can be placed once the tag census is revised.

Sections with support are `Stacks.LocalCohomology.sectionsWithSupportIn` and local cohomology is
`Stacks.LocalCohomology.localCohomologyWithSupportIn` applied to the module placed in degree zero;
the functorial packaging `Stacks.LocalCohomology.localCohomologyWithSupportInFunctor` is used
inside the proofs. The acyclicity of `T`-supported modules, which is what makes the reduction to
`M/Γ_T(M)` work, is
`Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_support_subset`.

That no associated prime of a module without `T`-supported sections lies in `T` is where stability
of `T` under specialization enters: an associated prime `p` is the annihilator of an element, so
`V(p) ⊆ T` would make that element a `T`-supported section, and `p ∈ T` forces `V(p) ⊆ T`.

## References

* [Faltings, *Über die Annullatoren lokaler Kohomologiegruppen*][Faltings-annulators]
* [Stacks Project, Tag 0AW8](https://stacks.math.columbia.edu/tag/0AW8)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Dividing out the sections with support in `T` -/

/-- If an element is a `T`-supported section and the prime `p` is not in `T`, some scalar outside
`p` kills it: otherwise the whole annihilator of the element would lie in `p`, putting `p` in the
zero locus of that annihilator, which is contained in `T`. -/
private lemma exists_smul_eq_zero_not_mem (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    {N : Type v} [AddCommGroup N] [Module A N] {y : N}
    (hy : y ∈ sectionsWithSupportIn A T N) {p : PrimeSpectrum A} (hp : p ∉ T) :
    ∃ c : A, c • y = 0 ∧ c ∉ p.asIdeal := by
  by_contra! h
  refine hp ((mem_sectionsWithSupportIn_iff A T N y).mp hy ?_)
  rw [PrimeSpectrum.mem_zeroLocus]
  intro c hc
  exact h c ((Ideal.mem_torsionOf_iff y c).mp hc)

/-- **A module has no sections with support in `T` once its `T`-supported sections are divided
out.** If the class of `x` is a `T`-supported section of `M/Γ_T(M)` and `p` is a prime containing
the annihilator of `x`, pick `c ∉ p` with `c • x ∈ Γ_T(M)` and then `d ∉ p` with `d • c • x = 0`;
then `d * c` annihilates `x` and lies outside the prime `p`, a contradiction. So `p` lies in `T`
for every such `p`, and `x` is itself a `T`-supported section. -/
theorem sectionsWithSupportIn_quotient_eq_bot (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : Type v) [AddCommGroup M] [Module A M] :
    sectionsWithSupportIn A T (M ⧸ sectionsWithSupportIn A T M) = ⊥ := by
  refine le_antisymm (fun ξ hξ ↦ ?_) bot_le
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, mem_sectionsWithSupportIn_iff]
  intro p hp
  by_contra hpT
  obtain ⟨c, hc0, hcp⟩ := exists_smul_eq_zero_not_mem A T hξ hpT
  have hcx : c • x ∈ sectionsWithSupportIn A T M := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, hc0]
  obtain ⟨d, hd0, hdp⟩ := exists_smul_eq_zero_not_mem A T hcx hpT
  rw [PrimeSpectrum.mem_zeroLocus] at hp
  have hdc : d * c ∈ p.asIdeal :=
    hp (by rw [SetLike.mem_coe, Ideal.mem_torsionOf_iff, mul_smul, hd0])
  rcases p.isPrime.mem_or_mem hdc with h | h
  · exact hdp h
  · exact hcp h

/-- The quotient of `M` by its sections with support in `T`. -/
abbrev quotientSectionsWithSupportIn (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) : ModuleCat.{max u v} A :=
  ModuleCat.of A ((M : Type (max u v)) ⧸ sectionsWithSupportIn A T (M : Type (max u v)))

/-- The inclusion of the sections with support in `T` into the module. -/
def sectionsWithSupportInι (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) : (sectionsWithSupportInFunctor.{u, v} A T).obj M ⟶ M :=
  ModuleCat.ofHom (sectionsWithSupportIn A T (M : Type (max u v))).subtype

/-- The projection of a module onto its quotient by the sections with support in `T`. -/
def quotientSectionsWithSupportInπ (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) : M ⟶ quotientSectionsWithSupportIn.{u, v} A T M :=
  ModuleCat.ofHom (sectionsWithSupportIn A T (M : Type (max u v))).mkQ

/-- The sections with support in `T` die in the quotient. -/
lemma sectionsWithSupportInι_comp_quotientSectionsWithSupportInπ (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) :
    sectionsWithSupportInι.{u, v} A T M ≫ quotientSectionsWithSupportInπ.{u, v} A T M = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).mpr x.property)

/-- **`0 → Γ_T(M) → M → M/Γ_T(M) → 0` is short exact.** -/
lemma sectionsWithSupportIn_shortExact (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) :
    (ShortComplex.mk (sectionsWithSupportInι.{u, v} A T M)
      (quotientSectionsWithSupportInπ.{u, v} A T M)
      (sectionsWithSupportInι_comp_quotientSectionsWithSupportInπ.{u, v} A T M)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    exact fun x hx ↦ ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).mp hx⟩, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).mpr fun _ _ h ↦ Subtype.ext h
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The quotient of a finite module by its sections with support in `T` is finite. -/
instance finite_quotientSectionsWithSupportIn (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A)
    [Module.Finite A (M : Type (max u v))] :
    Module.Finite A (quotientSectionsWithSupportIn.{u, v} A T M : Type (max u v)) :=
  Module.Finite.of_surjective (sectionsWithSupportIn A T (M : Type (max u v))).mkQ
    (Submodule.mkQ_surjective _)

/-- **The quotient map induces isomorphisms on local cohomology in positive degrees.** The
sections with support in `T` are acyclic for sections with support in `T`, so the long exact
sequence degenerates. -/
theorem isIso_localCohomologyMap_quotientSectionsWithSupportInπ (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) (i : ℤ) (hi : 0 < i) :
    IsIso (localCohomologyMap.{u, v} A T i (quotientSectionsWithSupportInπ.{u, v} A T M)) := by
  have hS := sectionsWithSupportIn_shortExact.{u, v} A T M
  have hvan : ∀ j : ℤ, 0 < j → IsZero (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        ((sectionsWithSupportInFunctor.{u, v} A T).obj M)) j) :=
    fun j hj ↦ isZero_localCohomologyWithSupportIn_of_support_subset.{u, v} A T hT _
      (support_sectionsWithSupportIn_subset T M) j hj
  have hmono : Mono (localCohomologyMap.{u, v} A T i
      (quotientSectionsWithSupportInπ.{u, v} A T M)) :=
    (ShortComplex.exact_iff_mono _ ((hvan i hi).eq_of_src _ _)).mp
      (localCohomology_exact₂.{u, v} T hS i)
  have hepi : Epi (localCohomologyMap.{u, v} A T i
      (quotientSectionsWithSupportInπ.{u, v} A T M)) :=
    (ShortComplex.exact_iff_epi _ ((hvan (i + 1) (by omega)).eq_of_tgt _ _)).mp
      (localCohomology_exact₃.{u, v} T hS i (i + 1) rfl)
  exact isIso_of_mono_of_epi _

/-! ### Finiteness in degrees at most zero -/

/-- A zero module is finite. -/
private lemma finite_of_isZero {A : Type u} [CommRing A] {X : ModuleCat.{max u v} A}
    (hX : IsZero X) : Module.Finite A (X : Type (max u v)) :=
  have : Subsingleton (X : Type (max u v)) := ModuleCat.isZero_iff_subsingleton.mp hX
  Module.Finite.of_surjective (0 : A →ₗ[A] (X : Type (max u v)))
    fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- Every scalar annihilates a zero module. -/
private lemma mem_annihilator_of_isZero {A : Type u} [CommRing A] {X : ModuleCat.{max u v} A}
    (hX : IsZero X) (r : A) : r ∈ Module.annihilator A (X : Type (max u v)) := by
  have := ModuleCat.isZero_iff_subsingleton.mp hX
  exact Module.mem_annihilator.mpr fun _ ↦ Subsingleton.elim _ _

/-- Local cohomology with support in `T` of a finite module is finite in degrees at most zero: it
vanishes in negative degrees and is a submodule of the module in degree zero. -/
theorem finite_localCohomologyWithSupportIn_of_nonpos (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A)
    [Module.Finite A (M : Type (max u v))] (i : ℤ) (hi : i ≤ 0) :
    Module.Finite A (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  rcases lt_or_eq_of_le hi with h | rfl
  · exact finite_of_isZero (isZero_localCohomologyWithSupportIn_of_neg.{u, v} T M i h)
  · exact finite_localCohomologyWithSupportIn_zero.{u, v} T (M : Type (max u v))

/-! ### Prime avoidance -/

/-- **No associated prime of a module without `T`-supported sections lies in `T`.** An associated
prime is the annihilator of an element; if it were in `T` then, `T` being stable under
specialization, its whole zero locus would be in `T` and the element would be a `T`-supported
section, hence zero, forcing the prime to be the unit ideal. -/
theorem notMem_of_mem_associatedPrimes_of_sectionsWithSupportIn_eq_bot (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type v) [AddCommGroup M] [Module A M] (hM : sectionsWithSupportIn A T M = ⊥)
    {p : Ideal A} (hp : p ∈ associatedPrimes A M) :
    (⟨p, hp.isPrime⟩ : PrimeSpectrum A) ∉ T := by
  intro hpT
  obtain ⟨x, hx⟩ := (isAssociatedPrime_iff.mp hp).2
  have hcol : Ideal.torsionOf A M x = p := by
    rw [hx]
    ext a
    rw [Ideal.mem_torsionOf_iff, Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hxmem : x ∈ sectionsWithSupportIn A T M := by
    rw [mem_sectionsWithSupportIn_iff]
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, hcol] at hq
    exact hT ((PrimeSpectrum.le_iff_specializes _ q).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal _ q).mp hq)) hpT
  have hx0 : x = 0 := by rwa [hM, Submodule.mem_bot] at hxmem
  refine hp.isPrime.ne_top ?_
  rw [← hcol, hx0, Ideal.eq_top_iff_one, Ideal.mem_torsionOf_iff, smul_zero]

/-- **Prime avoidance.** If `V(J) ⊆ T` and the finite module `M` has no `T`-supported sections,
some element of `J` is a nonzerodivisor on `M`: no associated prime of `M` contains `J`, there are
only finitely many of them, and their union is exactly the set of non-nonzerodivisors. -/
@[sga "2 III 2.1" "(iii) ⇒ (iv)"]
theorem exists_mem_isSMulRegular (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : sectionsWithSupportIn A T M = ⊥) (J : Ideal A)
    (hJ : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T) :
    ∃ f ∈ J, IsSMulRegular M f := by
  have hnot : ¬ ∃ p ∈ associatedPrimes A M, J ≤ p := by
    rintro ⟨p, hpmem, hle⟩
    refine notMem_of_mem_associatedPrimes_of_sectionsWithSupportIn_eq_bot A T hT M hM hpmem
      (hJ ?_)
    rwa [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  have hsub : ¬ ((J : Set A) ⊆ ⋃ p ∈ associatedPrimes A M, (p : Set A)) := by
    rwa [Ideal.subset_union_prime_finite (associatedPrimes.finite A M) ⊥ ⊥
      fun p hp _ _ ↦ hp.isPrime]
  obtain ⟨f, hfJ, hf⟩ := Set.not_subset.mp hsub
  refine ⟨f, hfJ, ?_⟩
  rw [biUnion_associatedPrimes_eq_compl_regular A M] at hf
  simpa using hf

/-! ### The annihilator of finite local cohomology -/

/-- Finitely many ideals, all of whose zero loci lie in `T` outside the negative range where the
ideal is the unit ideal, have a common lower bound whose zero locus lies in `T`: take the product
over the finite range. -/
private lemma exists_ideal_zeroLocus_subset_le (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (a : ℤ → Ideal A) (htop : ∀ i : ℤ, i < 0 → a i = ⊤) (n : ℕ)
    (hsub : ∀ i : ℤ, 0 ≤ i → i ≤ (n : ℤ) → PrimeSpectrum.zeroLocus (a i : Set A) ⊆ T) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ i : ℤ, i ≤ (n : ℤ) → J ≤ a i := by
  induction n with
  | zero =>
    refine ⟨a 0, hsub 0 le_rfl (by norm_num), fun i hi ↦ ?_⟩
    rcases lt_or_eq_of_le (show i ≤ 0 by exact_mod_cast hi) with h | rfl
    · simp [htop i h]
    · exact le_rfl
  | succ n ih =>
    obtain ⟨J, hJT, hJ⟩ := ih fun i h0 hin ↦ hsub i h0 (by omega)
    refine ⟨J * a ((n : ℤ) + 1), ?_, fun i hi ↦ ?_⟩
    · rw [PrimeSpectrum.zeroLocus_mul]
      exact Set.union_subset hJT (hsub ((n : ℤ) + 1) (by omega) (by omega))
    · rcases le_or_gt i (n : ℤ) with h | h
      · exact (Ideal.mul_le_inf.trans inf_le_left).trans (hJ i h)
      · obtain rfl : i = (n : ℤ) + 1 := by omega
        exact Ideal.mul_le_inf.trans inf_le_right

/-- **Finiteness implies annihilation by an ideal supported in `T`.** Each `H^i_T(M)` is finite,
hence annihilated by its own annihilator, whose zero locus is its support and so lies in `T`;
multiplying over `0 ≤ i ≤ n` gives one ideal. -/
theorem exists_ideal_zeroLocus_subset_le_annihilator_localCohomologyWithSupportIn (A : Type u)
    [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A)
    (n : ℕ)
    (hfin : ∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ i : ℤ, i ≤ (n : ℤ) → J ≤ Module.annihilator A (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  refine exists_ideal_zeroLocus_subset_le A T
    (fun i ↦ Module.annihilator A (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ?_ n ?_
  · intro i hi
    exact Submodule.eq_top_iff'.mpr
      (mem_annihilator_of_isZero (isZero_localCohomologyWithSupportIn_of_neg.{u, v} T M i hi))
  · intro i _ hin
    have := hfin i hin
    rw [← Module.support_eq_zeroLocus]
    exact support_localCohomologyWithSupportIn_subset.{u, v} T _ i

/-! ### Faltings' induction -/

/-- Multiplication by `r` is zero on a module exactly when `r` annihilates it. -/
private lemma smul_id_eq_zero_iff_mem_annihilator {A : Type u} [CommRing A]
    (X : ModuleCat.{max u v} A) (r : A) :
    r • 𝟙 X = 0 ↔ r ∈ Module.annihilator A (X : Type (max u v)) := by
  rw [Module.mem_annihilator]
  constructor
  · intro h m
    have h' := congrArg (fun φ : X ⟶ X ↦ φ.hom m) h
    simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, LinearMap.zero_apply] using h'
  · refine fun h ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    simpa only [ModuleCat.hom_smul, ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, LinearMap.zero_apply] using h m

/-- If `r` annihilates the source of a morphism, then `r` times that morphism is zero. -/
private lemma smul_eq_zero_of_smul_id_src {A : Type u} [CommRing A]
    {X Y : ModuleCat.{max u v} A} (r : A) (φ : X ⟶ Y) (h : r • 𝟙 X = 0) : r • φ = 0 := by
  rw [show r • φ = (r • 𝟙 X) ≫ φ by simp, h, Limits.zero_comp]

/-- If `r` annihilates the target of a morphism, then `r` times that morphism is zero. -/
private lemma smul_eq_zero_of_smul_id_tgt {A : Type u} [CommRing A]
    {X Y : ModuleCat.{max u v} A} (r : A) (φ : X ⟶ Y) (h : r • 𝟙 Y = 0) : r • φ = 0 := by
  rw [show r • φ = φ ≫ (r • 𝟙 Y) by simp, h, Limits.comp_zero]

/-- **The inductive step of Faltings' induction.** Let `M` be a finite module with no
`T`-supported sections and let `J` be an ideal with `V(J) ⊆ T` annihilating `H^i_T(M)` for
`i ≤ n + 1`. Choosing `f ∈ J` a nonzerodivisor on `M` makes multiplication by `f` act as zero on
all the modules in range, so the long exact sequence of `0 → M → M → M/fM → 0` breaks into short
exact sequences; these show that `J ^ 2` annihilates `H^i_T(M/fM)` for `i ≤ n`, and carry the
finiteness granted by the hypothesis `ih` back to `H^{i+1}_T(M)`. -/
private lemma finite_localCohomologyWithSupportIn_succ_of_sectionsWithSupportIn_eq_bot
    (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (n : ℕ)
    (ih : ∀ N : ModuleCat.{max u v} A, Module.Finite A (N : Type (max u v)) →
      ∀ K : Ideal A, PrimeSpectrum.zeroLocus (K : Set A) ⊆ T →
        (∀ j : ℤ, j ≤ (n : ℤ) → K ≤ Module.annihilator A (localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) j)) →
          ∀ j : ℤ, j ≤ (n : ℤ) → Module.Finite A (localCohomologyWithSupportIn A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) j))
    (M : ModuleCat.{max u v} A) [Module.Finite A (M : Type (max u v))]
    (hbot : sectionsWithSupportIn A T (M : Type (max u v)) = ⊥)
    (J : Ideal A) (hJT : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T)
    (hJann : ∀ j : ℤ, j ≤ (n : ℤ) + 1 → J ≤ Module.annihilator A
      (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) j)) :
    ∀ j : ℤ, 0 < j → j ≤ (n : ℤ) + 1 → Module.Finite A (localCohomologyWithSupportIn A T
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) j) := by
  obtain ⟨f, hfJ, hreg⟩ := exists_mem_isSMulRegular A T hT (M : Type (max u v)) hbot J hJT
  have hzero : (f • 𝟙 M) ≫ ModuleCat.ofHom
      (Submodule.mkQ (f • (⊤ : Submodule A (M : Type (max u v))))) = 0 :=
    (smulShortComplex.{u, v} f M).zero
  have hS : (ShortComplex.mk (f • 𝟙 M) (ModuleCat.ofHom
      (Submodule.mkQ (f • (⊤ : Submodule A (M : Type (max u v)))))) hzero).ShortExact :=
    smulShortComplex_shortExact.{u, v} hreg
  have hsmul0 : ∀ j : ℤ, j ≤ (n : ℤ) + 1 → ∀ r ∈ J,
      r • 𝟙 (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) j) = 0 :=
    fun j hj r hr ↦ (smul_id_eq_zero_iff_mem_annihilator _ r).mpr (hJann j hj hr)
  have hf0 : ∀ j : ℤ, j ≤ (n : ℤ) + 1 →
      localCohomologyMap.{u, v} A T j (f • 𝟙 M) = 0 := fun j hj ↦ by
    rw [localCohomologyMap_smul_id, hsmul0 j hj f hfJ]
  have hepiδ : ∀ (j j' : ℤ) (h : j + 1 = j'), j ≤ (n : ℤ) →
      Epi (localCohomologyδ.{u, v} T hS j j' h) := by
    intro j j' h hj
    exact (ShortComplex.exact_iff_epi _ (hf0 j' (by omega))).mp
      (localCohomology_exact₁.{u, v} T hS j j' h)
  have hJ2T : PrimeSpectrum.zeroLocus ((J ^ 2 : Ideal A) : Set A) ⊆ T :=
    (PrimeSpectrum.zeroLocus_pow J two_ne_zero).le.trans hJT
  have hJ2ann : ∀ j : ℤ, j ≤ (n : ℤ) → J ^ 2 ≤ Module.annihilator A
      (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A ((M : Type (max u v)) ⧸
            (f • (⊤ : Submodule A (M : Type (max u v))))))) j) := by
    intro j hj
    have : Mono (localCohomologyMap.{u, v} A T j (ModuleCat.ofHom
        (Submodule.mkQ (f • (⊤ : Submodule A (M : Type (max u v))))))) :=
      (ShortComplex.exact_iff_mono _ (hf0 j (by omega))).mp (localCohomology_exact₂.{u, v} T hS j)
    rw [pow_two]
    refine Ideal.mul_le.mpr fun a ha b hb ↦ ?_
    rw [← smul_id_eq_zero_iff_mem_annihilator]
    obtain ⟨w, hw⟩ := (localCohomology_exact₃.{u, v} T hS j (j + 1) rfl).lift' (b • 𝟙 _) (by
      rw [Linear.smul_comp, Category.id_comp,
        smul_eq_zero_of_smul_id_tgt b _ (hsmul0 (j + 1) (by omega) b hb)])
    rw [mul_smul, ← hw, ← Linear.comp_smul,
      smul_eq_zero_of_smul_id_src a _ (hsmul0 j (by omega) a ha), Limits.comp_zero]
  have hQ := ih (ModuleCat.of A ((M : Type (max u v)) ⧸
    (f • (⊤ : Submodule A (M : Type (max u v)))))) inferInstance (J ^ 2) hJ2T hJ2ann
  intro j hj0 hjn
  have hjj : j - 1 + 1 = j := by omega
  have := hQ (j - 1) (by omega)
  exact Module.Finite.of_surjective (localCohomologyδ.{u, v} T hS (j - 1) j hjj).hom
    ((ModuleCat.epi_iff_surjective _).mp (hepiδ (j - 1) j hjj (by omega)))

/-- **Stacks 0AW8, the implication (2) ⟹ (1).** If one ideal with zero locus inside `T`
annihilates `H^i_T(M)` for all `i ≤ n`, then those modules are finite. -/
private lemma finite_localCohomologyWithSupportIn_of_exists_annihilator (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) (n : ℕ) :
    ∀ M : ModuleCat.{max u v} A, Module.Finite A (M : Type (max u v)) →
      ∀ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T →
        (∀ i : ℤ, i ≤ (n : ℤ) → J ≤ Module.annihilator A (localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) →
          ∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A (localCohomologyWithSupportIn A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) := by
  induction n with
  | zero =>
    intro M hMfin _ _ _ i hi
    have := hMfin
    exact finite_localCohomologyWithSupportIn_of_nonpos.{u, v} A T M i (by exact_mod_cast hi)
  | succ n ih =>
    intro M hMfin J hJT hJann i hi
    have := hMfin
    rcases le_or_gt i 0 with hi0 | hi0
    · exact finite_localCohomologyWithSupportIn_of_nonpos.{u, v} A T M i hi0
    have hπiso : ∀ j : ℤ, 0 < j → IsIso (localCohomologyMap.{u, v} A T j
        (quotientSectionsWithSupportInπ.{u, v} A T M)) :=
      fun j hj ↦ isIso_localCohomologyMap_quotientSectionsWithSupportInπ.{u, v} A T hT M j hj
    have hM'bot : sectionsWithSupportIn A T
        (quotientSectionsWithSupportIn.{u, v} A T M : Type (max u v)) = ⊥ :=
      sectionsWithSupportIn_quotient_eq_bot A T (M : Type (max u v))
    have hM'ann : ∀ j : ℤ, j ≤ (n : ℤ) + 1 → J ≤ Module.annihilator A
        (localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
            (quotientSectionsWithSupportIn.{u, v} A T M)) j) := by
      intro j hj a ha
      rcases le_or_gt j 0 with hj0 | hj0
      · have hzero : IsZero (localCohomologyWithSupportIn A T
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
              (quotientSectionsWithSupportIn.{u, v} A T M)) j) := by
          rcases lt_or_eq_of_le hj0 with hjneg | hjzero
          · exact isZero_localCohomologyWithSupportIn_of_neg.{u, v} T _ j hjneg
          · subst hjzero
            refine IsZero.of_iso ?_
              (asIso ((sectionsToLocalCohomologyZero.{u, v} A T).app
                (quotientSectionsWithSupportIn.{u, v} A T M))).symm
            have hsub : Subsingleton ((sectionsWithSupportInFunctor.{u, v} A T).obj
                (quotientSectionsWithSupportIn.{u, v} A T M) : Type (max u v)) := by
              refine ⟨fun x y ↦ Subtype.ext ?_⟩
              have hx := hM'bot.le x.property
              have hy := hM'bot.le y.property
              rw [Submodule.mem_bot] at hx hy
              rw [hx, hy]
            exact ModuleCat.isZero_of_subsingleton _
        exact mem_annihilator_of_isZero hzero a
      · refine Module.mem_annihilator.mpr fun ξ ↦ ?_
        have := hπiso j hj0
        obtain ⟨ζ, hζ⟩ := (ModuleCat.epi_iff_surjective
          (localCohomologyMap.{u, v} A T j
            (quotientSectionsWithSupportInπ.{u, v} A T M))).mp inferInstance ξ
        rw [← hζ, ← map_smul, Module.mem_annihilator.mp (hJann j (by omega) ha) ζ, map_zero]
    have hM'fin := finite_localCohomologyWithSupportIn_succ_of_sectionsWithSupportIn_eq_bot.{u, v}
      A T hT n ih (quotientSectionsWithSupportIn.{u, v} A T M) hM'bot J hJT hM'ann
    have := hπiso i hi0
    have := hM'fin i hi0 (by exact_mod_cast hi)
    exact Module.Finite.equiv
      (asIso (localCohomologyMap.{u, v} A T i
        (quotientSectionsWithSupportInπ.{u, v} A T M))).toLinearEquiv.symm

/-! ### The criterion -/

/-- **Stacks 0AW8, equivalence of (1) and (2).** Let `A` be a Noetherian ring, `T ⊆ Spec(A)` a
subset stable under specialization, `M` a finite `A`-module and `n ≥ 0`. The local cohomology
modules `H^i_T(M)` are finite for every `i ≤ n` if and only if there is an ideal `J` with
`V(J) ⊆ T` annihilating `H^i_T(M)` for every `i ≤ n`.

Forward: a finite module is annihilated by its own annihilator, whose zero locus is its support,
and `H^i_T(M)` is supported in `T`. Backward: Faltings' induction on `n`, replacing `M` by
`M/Γ_T(M)` and using a nonzerodivisor in `J` to relate degree `i + 1` for `M` to degree `i` for
`M/fM`. -/
@[stacks 0AW8 "equivalence of (1) and (2)"]
theorem finite_localCohomologyWithSupportIn_iff_exists_annihilator (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{max u v} A) [Module.Finite A (M : Type (max u v))] (n : ℕ) :
    (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A (localCohomologyWithSupportIn A T
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
        ∀ i : ℤ, i ≤ (n : ℤ) → J ≤ Module.annihilator A (localCohomologyWithSupportIn A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
  ⟨exists_ideal_zeroLocus_subset_le_annihilator_localCohomologyWithSupportIn.{u, v} A T M n,
    fun ⟨J, hJT, hJann⟩ ↦ finite_localCohomologyWithSupportIn_of_exists_annihilator.{u, v}
      A T hT n M inferInstance J hJT hJann⟩

/-- **Stacks 0AW8 for closed support.** For `T = V(I)` the annihilating ideal of the criterion can
be taken to be a power of `I`: combine the equivalence of (1) and (2) with the equivalence of (2)
and (3), which is
`Stacks.LocalCohomology.exists_annihilator_iff_exists_power_annihilator`. -/
theorem finite_localCohomologyWithSupportIn_iff_exists_pow_annihilator (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{max u v} A)
    [Module.Finite A (M : Type (max u v))] (n : ℕ) :
    (∀ i : ℤ, i ≤ (n : ℤ) → Module.Finite A
        (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i)) ↔
      ∃ e : ℕ, ∀ i : ℤ, i ≤ (n : ℤ) → I ^ e ≤ Module.annihilator A
        (localCohomologyWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i) :=
  (finite_localCohomologyWithSupportIn_iff_exists_annihilator.{u, v} A
      (PrimeSpectrum.zeroLocus (I : Set A))
      (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization M n).trans
    (exists_annihilator_iff_exists_power_annihilator.{u, v} A I M n)

end Stacks.LocalCohomology

end
