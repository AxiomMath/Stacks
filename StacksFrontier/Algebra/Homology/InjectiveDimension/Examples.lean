module

public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.GlobalDimension.Cyclic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Two computations of injective dimension

Over a field, the residue field of the ring of dual numbers has a left-unbounded resolution whose
terms are copies of the ring and whose differentials are multiplication by the nilpotent element.
Although the ring is injective as a module over itself, the residue field does not have finite
injective dimension.

At the opposite extreme, every ideal of a Dedekind domain is a finite projective module.
Consequently cyclic modules have projective dimension at most one, all modules have injective
dimension at most one, higher Ext groups vanish, and every bounded object of the derived category
of modules splits as the finite direct sum of its cohomology modules in their respective degrees.

## Main definitions

This file introduces no new definitions. The ring of dual numbers and its element `ε` are
represented by Mathlib's `DualNumber` and `DualNumber.eps`.

## Main results

* `StacksDraft.InjectiveDimension.dualNumber_residueField_infinite_injectiveDimension`: the
  periodic resolution, the self-injectivity of the dual numbers, and the infinitude of the
  injective dimension of their residue field.
* `StacksDraft.InjectiveDimension.dedekindDomain_ideal_projective_and_bounded_complex_splitting`:
  the projectivity, homological-dimension, Ext-vanishing and derived splitting consequences for a
  Dedekind domain.

## Implementation notes

For the dual numbers, the displayed complex is cohomologically indexed, supported in degrees at
most zero, and augmented in degree zero by the quotient map; thus its arrows point from the
unbounded negative direction toward the residue field. The concrete pair model `DualNumber k` is
Mathlib's standard realization of `k[x] / (x²)`.

Stacks 0AUW(2), `projective_of_finite_isTorsionFree` — a finite torsion-free module over
a Dedekind
domain is projective — is the content of Stacks 0AUW (2), which belongs to another cluster. It is
kept private and untagged here, and is a dedup target: once the provider of 0AUW lands, this copy
should be deleted and its single use below repointed at that provider. It is two steps from
Mathlib (`Module.finitePresentation_of_finite` followed by
`Module.Flat.projective_of_finitePresentation`, flatness coming from the Dedekind torsion-free
instance), so nothing of substance is duplicated.

For a Dedekind domain, projective and injective dimension one are expressed as upper bounds, as
required by the dimension argument and also valid for zero objects. Since a Dedekind domain is
Noetherian and the zero ideal is projective, the ideal statement is harmlessly strengthened from
nonzero ideals to all ideals. Boundedness is represented by `IsGE` and `IsLE`, and the direct sum
is the finite biproduct over the corresponding interval.

## References

* [Stacks Project, Tag 0A5U](https://stacks.math.columbia.edu/tag/0A5U)
* [Stacks Project, Tag 0EX0](https://stacks.math.columbia.edu/tag/0EX0)
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.InjectiveDimension

universe u v

section DualNumbers

private theorem selfInjective (k : Type u) [Field k] :
    Module.Injective (DualNumber k) (DualNumber k) := by
  apply Module.Baer.injective
  intro I g
  rcases DualNumber.ideal_trichotomy I with rfl | rfl | rfl
  · refine ⟨0, ?_⟩
    intro x hx
    subst x
    show 0 = g 0
    simp
  · let y : DualNumber k := g ⟨DualNumber.eps, Ideal.mem_span_singleton_self _⟩
    have hy : DualNumber.eps * y = 0 := by
      have he : (DualNumber.eps : DualNumber k) * DualNumber.eps = 0 := by ext <;> simp
      have hh : (DualNumber.eps : DualNumber k) •
          (⟨DualNumber.eps, Ideal.mem_span_singleton_self _⟩ :
            Ideal.span ({DualNumber.eps} : Set (DualNumber k))) = 0 := by
        apply Subtype.ext
        simp
      calc
        DualNumber.eps * y = g ((DualNumber.eps : DualNumber k) •
            (⟨DualNumber.eps, Ideal.mem_span_singleton_self _⟩ :
              Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) := by
          show (DualNumber.eps : DualNumber k) • y = _
          exact (map_smul g DualNumber.eps _).symm
        _ = g 0 := congrArg g hh
        _ = 0 := map_zero g
    have hfst : y.fst = 0 := by
      have hh := congrArg TrivSqZeroExt.snd hy
      simpa using hh
    obtain ⟨z, hz⟩ := DualNumber.fst_eq_zero_iff_eps_dvd.mp hfst
    refine ⟨LinearMap.mulRight (DualNumber k) z, ?_⟩
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have : g ⟨a * DualNumber.eps, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)⟩ =
        a * y := by
      show g (a • (⟨DualNumber.eps, Ideal.mem_span_singleton_self _⟩ :
        Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) = a • y
      exact map_smul g a _
    rw [this, hz]
    simp [mul_comm, mul_left_comm]
  · refine ⟨LinearMap.mulRight (DualNumber k) (g ⟨1, by simp⟩), ?_⟩
    intro x hx
    have : g ⟨x, hx⟩ = x * g ⟨1, by simp⟩ := by
      simpa using (map_smul g x (⟨1, by simp⟩ : (⊤ : Ideal (DualNumber k))))
    simpa using this.symm

private theorem epsSq (k : Type u) [Field k] :
    (DualNumber.eps : DualNumber k) * DualNumber.eps = 0 := by
  ext <;> simp

private theorem epsMul_comp_epsMul (k : Type u) [Field k] :
    ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (DualNumber.eps : DualNumber k)) ≫
      ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (DualNumber.eps : DualNumber k)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show DualNumber.eps * (DualNumber.eps * x) = 0
  rw [← mul_assoc, epsSq]
  simp

private theorem epsKer (k : Type u) [Field k] :
    LinearMap.ker (LinearMap.mulLeft (DualNumber k) DualNumber.eps) =
      Ideal.span ({DualNumber.eps} : Set (DualNumber k)) := by
  ext x
  constructor
  · intro hx
    have hh := congrArg TrivSqZeroExt.snd
      (show (DualNumber.eps : DualNumber k) * x = 0 from hx)
    have hfst : x.fst = 0 := by simpa using hh
    obtain ⟨a, ha⟩ := DualNumber.fst_eq_zero_iff_eps_dvd.mp hfst
    rw [ha]
    simpa [mul_comm] using
      (Ideal.span ({DualNumber.eps} : Set (DualNumber k))).mul_mem_left a
        (Ideal.mem_span_singleton_self _)
  · intro hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
    show (DualNumber.eps : DualNumber k) * x = 0
    rw [← ha, mul_comm a DualNumber.eps, ← mul_assoc, epsSq]
    simp

private theorem epsRange (k : Type u) [Field k] :
    LinearMap.range (LinearMap.mulLeft (DualNumber k) DualNumber.eps) =
      Ideal.span ({DualNumber.eps} : Set (DualNumber k)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simpa [mul_comm] using
      (Ideal.span ({DualNumber.eps} : Set (DualNumber k))).mul_mem_left a
        (Ideal.mem_span_singleton_self _)
  · intro hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
    refine ⟨a, ?_⟩
    show DualNumber.eps * a = x
    rw [mul_comm]
    exact ha

private theorem epsSmulQuotient (k : Type u) [Field k]
    (y : DualNumber k ⧸ Ideal.span ({DualNumber.eps} : Set (DualNumber k))) :
    (DualNumber.eps : DualNumber k) • y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | _ x =>
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (Ideal.span ({DualNumber.eps} : Set (DualNumber k))).mul_mem_right x
      (Ideal.mem_span_singleton_self _)

private theorem quotient_one_ne_zero (k : Type u) [Field k] :
    (Submodule.Quotient.mk (1 : DualNumber k) :
      DualNumber k ⧸ Ideal.span ({DualNumber.eps} : Set (DualNumber k))) ≠ 0 := fun h =>
  DualNumber.isMaximal_span_singleton_eps.ne_top
    ((Ideal.eq_top_iff_one _).mpr ((Submodule.Quotient.mk_eq_zero _).mp h))

private theorem residueNotInjective (k : Type u) [Field k] :
    ¬ Module.Injective (DualNumber k)
      (DualNumber k ⧸ Ideal.span ({DualNumber.eps} : Set (DualNumber k))) := by
  let I : Ideal (DualNumber k) := Ideal.span {DualNumber.eps}
  let f : (DualNumber k ⧸ I) →ₗ[DualNumber k] DualNumber k :=
    I.liftQ (LinearMap.mulLeft (DualNumber k) DualNumber.eps) (le_of_eq (epsKer k).symm)
  have hf : Function.Injective f := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' I _ (epsKer k).symm)
  intro hi
  let : Module.Injective (DualNumber k) (DualNumber k ⧸ I) := hi
  obtain ⟨g, hg⟩ := Module.Injective.out f hf (LinearMap.id)
  apply quotient_one_ne_zero k
  have h1 := hg (Submodule.Quotient.mk (1 : DualNumber k) : DualNumber k ⧸ I)
  have hf1 : f (Submodule.Quotient.mk (1 : DualNumber k)) = DualNumber.eps := by
    show (I.liftQ (LinearMap.mulLeft (DualNumber k) DualNumber.eps) _)
      (Submodule.Quotient.mk 1) = _
    rw [Submodule.liftQ_apply]
    simp
  rw [hf1] at h1
  have heps : g DualNumber.eps = 0 := by
    calc
      g DualNumber.eps = g ((DualNumber.eps : DualNumber k) • 1) := by simp
      _ = DualNumber.eps • g 1 := map_smul g _ _
      _ = 0 := epsSmulQuotient k _
  simpa [heps] using h1.symm

private theorem noFiniteFixpoint (d : WithBot ℕ∞) (n : ℕ)
    (h0 : (0 : WithBot ℕ∞) ≤ d) (hn : d ≤ n) : d ≠ d + 1 := by
  cases d with
  | bot => simp at h0
  | coe a =>
    cases a with
    | top =>
      norm_cast at hn
    | coe m =>
      exact ne_of_lt (by exact_mod_cast Nat.lt_succ_self m)

private theorem residueInfiniteDimension (k : Type u) [Field k] :
    ∀ n : ℕ, ¬ HasInjectiveDimensionLE
      (ModuleCat.of (DualNumber k)
        (DualNumber k ⧸ Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) n := by
  let R := DualNumber k
  let I : Ideal R := Ideal.span {DualNumber.eps}
  let M := R ⧸ I
  let f : M →ₗ[R] R := I.liftQ (LinearMap.mulLeft R DualNumber.eps)
    (le_of_eq (epsKer k).symm)
  let g : R →ₗ[R] M := I.mkQ
  have hRange : f.range = I := (Submodule.range_liftQ I _ _).trans (epsRange k)
  have hKer : g.ker = I := Submodule.ker_mkQ I
  have hfg : g ∘ₗ f = 0 := LinearMap.range_le_ker_iff.mp (hRange.le.trans hKer.ge)
  let S := ModuleCat.shortComplexOfCompEqZero f g hfg
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_iff.mpr (hKer.trans hRange.symm))
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' I _ (epsKer k).symm))
    (Submodule.mkQ_surjective I)
  have hInj : Injective S.X₂ :=
    (Module.injective_iff_injective_object R R).mp (selfInjective k)
  have hNotInj : ¬ Injective S.X₁ := by
    intro h
    exact residueNotInjective k
      ((Module.injective_iff_injective_object R M).mpr h)
  have hEq := hS.injectiveDimension_X₁_eq_succ_of_not_injective hInj hNotInj
  intro n hn
  have hNZ : ¬ IsZero S.X₁ := by
    intro h
    have := ModuleCat.isZero_iff_subsingleton.mp h
    exact quotient_one_ne_zero k (Subsingleton.elim _ _)
  have h0 : (0 : WithBot ℕ∞) ≤ injectiveDimension S.X₁ :=
    (injectiveDimension_ge_zero_iff S.X₁).mpr hNZ
  have hle : injectiveDimension S.X₁ ≤ n :=
    (injectiveDimension_le_iff S.X₁ n).mpr hn
  exact (noFiniteFixpoint _ n h0 hle) hEq

private abbrev periodicX (k : Type u) [Field k] (i : ℤ) :
    ModuleCat (DualNumber k) :=
  if i ≤ 0 then ModuleCat.of (DualNumber k) (DualNumber k) else
    ModuleCat.of (DualNumber k) (Fin 0 → DualNumber k)

private def periodicD (k : Type u) [Field k] (i : ℤ) :
    periodicX k i ⟶ periodicX k (i + 1) :=
  if h : i < 0 then
    eqToHom (by simp only [periodicX, ite_eq_left (show i ≤ 0 by omega)]) ≫
      ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (DualNumber.eps : DualNumber k)) ≫
        eqToHom (by simp only [periodicX, ite_eq_left (show i + 1 ≤ 0 by omega)])
  else 0

private theorem periodicD_neg (k : Type u) [Field k] (i : ℤ) (hi : i < 0) :
    periodicD k i = eqToHom (by simp only [periodicX, ite_eq_left (show i ≤ 0 by omega)]) ≫
      ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (DualNumber.eps : DualNumber k)) ≫
        eqToHom (by simp only [periodicX, ite_eq_left (show i + 1 ≤ 0 by omega)]) := by
  simp [periodicD, hi]

private theorem periodicD_nonneg (k : Type u) [Field k] (i : ℤ) (hi : 0 ≤ i) :
    periodicD k i = 0 := by
  simp [periodicD, show ¬ i < 0 by omega]

private theorem isZero_periodicX_of_pos (k : Type u) [Field k] (i : ℤ) (hi : 0 < i) :
    IsZero (periodicX k i) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  show Subsingleton (periodicX k i)
  rw [show periodicX k i = ModuleCat.of (DualNumber k) (Fin 0 → DualNumber k) by
    simp [periodicX, show ¬ i ≤ 0 by omega]]
  exact ⟨fun a b => funext (fun j => Fin.elim0 j)⟩

private theorem periodicDSq (k : Type u) [Field k] (i : ℤ) :
    periodicD k i ≫ periodicD k (i + 1) = 0 := by
  by_cases hi : i < 0
  · by_cases hj : i + 1 < 0
    · simp only [periodicX, periodicD, hi, ↓reduceDIte, hj, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Preadditive.IsIso.comp_left_eq_zero]
      rw [← Category.assoc, epsMul_comp_epsMul, zero_comp]
    · rw [periodicD_nonneg k (i + 1) (by omega), comp_zero]
  · rw [periodicD_nonneg k i (by omega), zero_comp]

private abbrev periodicK (k : Type u) [Field k] :
    CochainComplex (ModuleCat (DualNumber k)) ℤ :=
  CochainComplex.of (periodicX k) (periodicD k) (periodicDSq k)

private noncomputable def periodicQ (k : Type u) [Field k] :
    periodicK k ⟶ (CochainComplex.singleFunctor (ModuleCat (DualNumber k)) 0).obj
      (ModuleCat.of (DualNumber k)
        (DualNumber k ⧸ Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) :=
  HomologicalComplex.mkHomToSingle
    (ModuleCat.ofHom (Submodule.mkQ
      (Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) :
      (periodicK k).X 0 ⟶ _) (by
    intro i hi
    have hii : i = -1 := by
      change i + 1 = 0 at hi
      omega
    subst i
    change (periodicD k (-1)) ≫
      ModuleCat.ofHom (Submodule.mkQ
        (Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) = 0
    simp only [Int.reduceNeg, periodicX, Left.neg_nonpos_iff, zero_le_one, ↓dreduceIte,
      Int.reduceAdd, Std.le_refl, periodicD, Int.neg_neg_iff_pos, zero_lt_one, ↓reduceDIte,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((Ideal.span ({DualNumber.eps} : Set (DualNumber k))).mul_mem_right x
        (Ideal.mem_span_singleton_self _)))

private theorem periodicQ_f_zero (k : Type u) [Field k] :
    (periodicQ k).f 0 = ModuleCat.ofHom (Submodule.mkQ
      (Ideal.span ({DualNumber.eps} : Set (DualNumber k)))) := by
  simp [periodicQ, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rfl

private def periodicE (k : Type u) [Field k] (i : ℤ) (hi : i ≤ 0) :
    periodicX k i ≅ ModuleCat.of (DualNumber k) (DualNumber k) :=
  eqToIso (by simp [periodicX, hi])

private theorem periodicExactAt (k : Type u) [Field k] (i : ℤ) (hi : i < 0) :
    (periodicK k).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  have hidx : i - 1 + 1 = i := by omega
  let f : ModuleCat.of (DualNumber k) (DualNumber k) ⟶
      ModuleCat.of (DualNumber k) (DualNumber k) :=
    ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (DualNumber.eps : DualNumber k))
  let S : ShortComplex (ModuleCat (DualNumber k)) :=
    ShortComplex.mk f f (epsMul_comp_epsMul k)
  have hS : S.Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (epsRange k).trans (epsKer k).symm
  apply (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk (S₂ := S) (periodicE k (i - 1) (by omega))
      (periodicE k i (by omega)) (periodicE k (i + 1) (by omega))
      (by
        show (periodicE k (i - 1) (by omega)).hom ≫ f =
          (periodicK k).d (i - 1) i ≫ (periodicE k i (by omega)).hom
        simp only [periodicK, CochainComplex.of.d, hidx, periodicE, eqToIso.hom]
        simp only [dite_eq_left trivial]
        rw [periodicD_neg k (i - 1) (by omega)]
        dsimp [f]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
      (by
        show (periodicE k i (by omega)).hom ≫ f =
          (periodicK k).d i (i + 1) ≫ (periodicE k (i + 1) (by omega)).hom
        simp only [periodicK, CochainComplex.of_d, periodicE, eqToIso.hom]
        rw [periodicD_neg k i hi]
        dsimp [f]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]))).2
  exact hS

private theorem periodicExactAt_pos (k : Type u) [Field k] (i : ℤ) (hi : 0 < i) :
    (periodicK k).ExactAt i := by
  exact ShortComplex.exact_of_isZero_X₂ _ (isZero_periodicX_of_pos k i hi)

private theorem periodicQ_quasiIso (k : Type u) [Field k] :
    QuasiIso (periodicQ k) := by
  constructor
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff' (periodicQ k) (-1) 0 1
      (by simp) (by simp)]
    rw [ShortComplex.quasiIso_iff_of_zeros']
    · constructor
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        show LinearMap.range ((periodicK k).d (-1) 0).hom =
          LinearMap.ker ((periodicQ k).f 0).hom
        rw [periodicQ_f_zero]
        simp only [periodicK, periodicX, Std.le_refl, ↓dreduceIte, Int.reduceNeg,
          Left.neg_nonpos_iff, zero_le_one, CochainComplex.of.d, neg_add_cancel, ↓reduceDIte,
          Int.reduceAdd, periodicD, Int.neg_neg_iff_pos, zero_lt_one, eqToHom_refl,
          Category.comp_id, Category.id_comp, ConcreteCategory.hom_ofHom, epsRange]
        show Ideal.span ({DualNumber.eps} : Set (DualNumber k)) =
          (Submodule.mkQ (Ideal.span ({DualNumber.eps} : Set (DualNumber k)))).ker
        rw [Submodule.ker_mkQ]
      · show Epi ((periodicQ k).f 0)
        rw [periodicQ_f_zero]
        apply (ModuleCat.epi_iff_surjective _).mpr
        exact Submodule.mkQ_surjective _
    · simp [periodicK, CochainComplex.of.d, periodicD]
    · simp
    · simp
  · exact (quasiIsoAt_iff_exactAt' (periodicQ k) i
      (HomologicalComplex.exactAt_single_obj _ _ _ _ hi)).2
      ((lt_or_gt_of_ne hi).elim (periodicExactAt k i) (periodicExactAt_pos k i))

/-- **Stacks 0A5U.** Let `R` be the ring of dual numbers over a field and let `M = R/(ε)`.
Then `R` is injective as an `R`-module, `M` is quasi-isomorphic to the left-unbounded complex of
copies of `R` whose differentials are multiplication by `ε`, and `M` has infinite injective
dimension. -/
@[stacks 0A5U]
public theorem dualNumber_residueField_infinite_injectiveDimension (k : Type u) [Field k] :
    let R := DualNumber k
    let M := ModuleCat.of R (R ⧸ Ideal.span ({DualNumber.eps} : Set R))
    Module.Injective R R ∧
      (∃ (K : CochainComplex (ModuleCat R) ℤ)
          (e : ∀ (i : ℤ) (_ : i ≤ 0), K.X i ≅ ModuleCat.of R R)
          (q : K ⟶ (CochainComplex.singleFunctor (ModuleCat R) 0).obj M),
        QuasiIso q ∧
          (q.f 0 = (e 0 (by omega)).hom ≫
            ModuleCat.ofHom (Submodule.mkQ (Ideal.span ({DualNumber.eps} : Set R)))) ∧
          (∀ (i : ℤ) (hi : i < 0),
            (e i (by omega)).hom ≫ ModuleCat.ofHom (LinearMap.mulLeft R DualNumber.eps) =
              K.d i (i + 1) ≫ (e (i + 1) (by omega)).hom) ∧
          (∀ (i : ℤ), 0 < i → IsZero (K.X i))) ∧
      (∀ n : ℕ, ¬ HasInjectiveDimensionLE M n) := by
  dsimp
  refine ⟨selfInjective k, ⟨periodicK k, periodicE k, periodicQ k,
    periodicQ_quasiIso k, ?_, ?_, ?_⟩, residueInfiniteDimension k⟩
  · rw [periodicQ_f_zero]
    simp [periodicE, periodicX]
    rfl
  · intro i hi
    show (periodicE k i (by omega)).hom ≫
      ModuleCat.ofHom (LinearMap.mulLeft (DualNumber k) (DualNumber.eps : DualNumber k)) =
      (periodicK k).d i (i + 1) ≫ (periodicE k (i + 1) (by omega)).hom
    simp only [periodicK, CochainComplex.of_d]
    rw [periodicD_neg k i hi]
    simp only [periodicE, eqToIso.hom]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · exact fun i hi => isZero_periodicX_of_pos k i hi

end DualNumbers

section DedekindDomain

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0EX0.** Ideals over a Dedekind domain are finite projective. Hence cyclic modules
have projective dimension at most one, every module has injective dimension at most one, all Ext
groups in degrees at least two vanish, and every bounded derived object is isomorphic to the
finite direct sum of its cohomologies placed in their degrees. -/
@[stacks 0EX0]
public theorem dedekindDomain_ideal_projective_and_bounded_complex_splitting
    (R : Type u) [CommRing R] [IsDedekindDomain R] [Small.{v} R] :
    (∀ I : Ideal R, Module.Finite R I ∧ Module.Projective R I) ∧
      (∀ I : Ideal R,
        HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ I))) 1) ∧
      (∀ M : ModuleCat.{v} R, HasInjectiveDimensionLE M 1) ∧
      (∀ (M N : ModuleCat.{v} R) (i : ℕ), 2 ≤ i →
        Subsingleton (Abelian.Ext M N i)) ∧
      ∀ (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ), K.IsGE a → K.IsLE b →
        Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
          (DerivedCategory.singleFunctor (ModuleCat.{v} R) i.1).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i.1).obj K)) := by
  have hIdeal : ∀ I : Ideal R, Module.Finite R I ∧ Module.Projective R I := fun I => by
    have : Module.Finite R I := inferInstance
    exact ⟨inferInstance, _root_.projective_of_finite_isTorsionFree R I⟩
  have hpd : ∀ I : Ideal R,
      HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ I))) 1 := fun I => by
    have hexact : Function.Exact I.subtype I.mkQ := LinearMap.exact_subtype_mkQ I
    let S := ModuleCat.shortComplexOfConj (Shrink.linearEquiv R I) (Shrink.linearEquiv R R)
      (Shrink.linearEquiv R (R ⧸ I)) _ _ hexact.linearMap_comp_eq_zero
    have hS : S.ShortExact :=
      ModuleCat.shortComplexOfConj_shortExact _ _ _ _ _ hexact I.subtype_injective
        I.mkQ_surjective
    have hI : Projective S.X₁ := by
      dsimp [S]
      let : Module.Projective R I := (hIdeal I).2
      exact (IsProjective.iff_projective _).mp
        (Module.Projective.of_equiv' (Shrink.linearEquiv R I).symm)
    let : Projective S.X₁ := hI
    simpa [S] using hS.hasProjectiveDimensionLT_X₃ 1
      (inferInstance : HasProjectiveDimensionLT S.X₁ 1)
      (inferInstance : HasProjectiveDimensionLT S.X₂ 2)
  have hcyclic : ∀ I : Ideal R,
      HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) 1 := fun I => by
    let := hpd I
    exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := ModuleCat.of R (Shrink.{v} (R ⧸ I))) (N := ModuleCat.of R (R ⧸ I))
      (Shrink.linearEquiv R (R ⧸ I)) 1
  have hall : ∀ N : ModuleCat.{v} R, HasProjectiveDimensionLE N 1 :=
    ((ringGlobalDimension_lt_tfae R 2).out 4 2).mp hcyclic
  have hinj : ∀ M : ModuleCat.{v} R, HasInjectiveDimensionLE M 1 := fun M => by
    show HasInjectiveDimensionLT M 2
    rw [hasInjectiveDimensionLT_iff]
    intro i hi N e
    let := hall N
    exact e.eq_zero_of_hasProjectiveDimensionLT 2 hi
  have hext : ∀ (M N : ModuleCat.{v} R) (i : ℕ), 2 ≤ i →
      Subsingleton (Abelian.Ext M N i) := fun M N i hi => by
    let := hinj N
    exact HasInjectiveDimensionLT.subsingleton N 2 i hi M
  refine ⟨hIdeal, hpd, hinj, hext, ?_⟩
  intro K a b hge hle
  let := hge
  let := hle
  apply DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_two_eq_zero
  intro A B e
  let := hext B A 2 (by omega)
  exact Subsingleton.elim e 0

end DedekindDomain

end StacksDraft.InjectiveDimension
