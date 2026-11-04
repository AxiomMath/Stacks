module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroup
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Modules of finite length

The modules of finite length over a ring form a Serre class of the category of modules, and
length is a homomorphism from its Grothendieck group to `ℤ`. Over a Noetherian ring of Krull
dimension at most one, a finite module each of whose elements is killed by a non-zero-divisor
has finite length.

## Main definitions

* `ModuleCat.isFiniteLength`: the modules of finite length, as a property of objects of
  `ModuleCat O`.
* `ModuleCat.finiteLengthHom`: the homomorphism `K₀(modules of finite length) → ℤ` given by
  length.

## Main results

* `ModuleCat.isSerreClass_isFiniteLength`: the modules of finite length form a Serre class.
* `isFiniteLength_of_forall_exists_smul_eq_zero`: a finite torsion module over a Noetherian
  ring of dimension at most one has finite length.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **A finite module all of whose elements are killed by non-zero-divisors has finite length**,
over a Noetherian ring of Krull dimension at most one. One non-zero-divisor `a` kills a finite
set of generators, so the module is a quotient of a finite power of `O ⧸ (a)`, which has finite
length. -/
@[ega "IV 21.10.13" "more general"]
theorem isFiniteLength_of_forall_exists_smul_eq_zero {O M : Type*} [CommRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] [AddCommGroup M] [Module O M] [Module.Finite O M]
    (h : ∀ m : M, ∃ a ∈ nonZeroDivisors O, a • m = 0) : IsFiniteLength O M := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  choose c hc hcm using fun i : Fin n => h (f (Pi.single i 1))
  set a : O := ∏ i, c i with ha
  have haO : a ∈ nonZeroDivisors O := prod_mem fun i _ => hc i
  have hai (i : Fin n) : a • f (Pi.single i 1) = 0 := by
    rw [ha, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hcm i, smul_zero]
  let φ : (Fin n → O ⧸ Ideal.span {a}) →ₗ[O] M :=
    ∑ i : Fin n, ((Ideal.span {a}).liftQ (LinearMap.toSpanSingleton O M (f (Pi.single i 1)))
      (by
        rw [Ideal.span_le]
        rintro _ rfl
        exact hai i)) ∘ₗ LinearMap.proj i
  have hφ : Function.Surjective φ := by
    intro m
    obtain ⟨v, rfl⟩ := hf m
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    calc φ (fun i => Submodule.Quotient.mk (v i)) = ∑ i, v i • f (Pi.single i 1) := by
          simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply,
            LinearMap.proj_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
      _ = f (∑ i, v i • Pi.single i 1) := by simp [map_sum, map_smul]
      _ = f v := by
          congr 1
          ext j
          simp [Finset.sum_apply, Pi.single_apply]
  have hlen : Module.length O (Fin n → O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Module.length_pi_of_fintype]
    exact ENat.sum_ne_top.2 fun i _ =>
      Module.length_ne_top_iff.2 (isFiniteLength_quotient_span_singleton O haO)
  exact Module.length_ne_top_iff.1
    (ne_top_of_le_ne_top hlen (Module.length_le_of_surjective φ hφ))

namespace ModuleCat

variable (O : Type u) [Ring O]

/-- The modules of finite length over a ring, as a property of objects of `ModuleCat O`. -/
def isFiniteLength : ObjectProperty (ModuleCat.{u} O) := fun M => IsFiniteLength O M

/-- **The modules of finite length form a Serre class**: length does not grow along a submodule
or a quotient, and it is additive along a short exact sequence. -/
instance isSerreClass_isFiniteLength : (isFiniteLength O).IsSerreClass where
  exists_zero := ⟨ModuleCat.of O PUnit, isZero_of_subsingleton _,
    Module.length_ne_top_iff.1 (by rw [Module.length_eq_zero]; exact ENat.zero_ne_top)⟩
  prop_of_mono {M N} f hf hN := by
    rw [ModuleCat.mono_iff_injective] at hf
    exact Module.length_ne_top_iff.1
      (ne_top_of_le_ne_top (Module.length_ne_top_iff.2 hN)
        (Module.length_le_of_injective f.hom hf))
  prop_of_epi {M N} f hf hM := by
    rw [ModuleCat.epi_iff_surjective] at hf
    exact Module.length_ne_top_iff.1
      (ne_top_of_le_ne_top (Module.length_ne_top_iff.2 hM)
        (Module.length_le_of_surjective f.hom hf))
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have h := Module.length_eq_add_of_exact S.f.hom S.g.hom
      ((ModuleCat.mono_iff_injective _).1 hS.mono_f) ((ModuleCat.epi_iff_surjective _).1 hS.epi_g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
    exact Module.length_ne_top_iff.1 (h ▸ WithTop.add_ne_top.2
      ⟨Module.length_ne_top_iff.2 h₁, Module.length_ne_top_iff.2 h₃⟩)

/-- **Length is additive along a short exact sequence of modules of finite length.** -/
theorem length_toNat_add_of_shortExact {S : ShortComplex (isFiniteLength O).FullSubcategory}
    (hS : S.ShortExact) :
    ((Module.length O S.X₂.obj).toNat : ℤ) =
      (Module.length O S.X₁.obj).toNat + (Module.length O S.X₃.obj).toNat := by
  have := (isFiniteLength O).preservesFiniteLimits_ι_of_isWeakSerreClass
  have := (isFiniteLength O).preservesFiniteColimits_ι_of_isWeakSerreClass
  have hS' := hS.map_of_exact (isFiniteLength O).ι
  have h := Module.length_eq_add_of_exact (S.map (isFiniteLength O).ι).f.hom
    (S.map (isFiniteLength O).ι).g.hom
    ((ModuleCat.mono_iff_injective _).1 hS'.mono_f) ((ModuleCat.epi_iff_surjective _).1 hS'.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS'.exact)
  have h₁ := Module.length_ne_top_iff.2 S.X₁.property
  have h₃ := Module.length_ne_top_iff.2 S.X₃.property
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    ObjectProperty.ι_obj] at h
  rw [h, ENat.toNat_add h₁ h₃]
  push_cast
  rfl

/-- **The length homomorphism** `K₀(modules of finite length) → ℤ`. -/
def finiteLengthHom : KZero (isFiniteLength O).FullSubcategory →+ ℤ :=
  KZero.lift (fun M => ((Module.length O M.obj).toNat : ℤ))
    fun _ hS => length_toNat_add_of_shortExact O hS

/-- The length homomorphism sends the class of a module to its length. -/
theorem finiteLengthHom_mk (M : (isFiniteLength O).FullSubcategory) :
    finiteLengthHom O (KZero.mk _ M) = (Module.length O M.obj).toNat :=
  KZero.lift_mk _ _ M

end ModuleCat

end
