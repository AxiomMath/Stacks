module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Function fields of transcendence degree one

Let `K` be a field extension of `k` which is finitely generated, as a field, and has
transcendence degree one. Then `K` is a function field over `k` in the sense of Mathlib's
`FunctionField`: for any element `t ∈ K` transcendental over `k`, the embedding
`k(X) → K, X ↦ t` makes `K` a finite extension of the rational function field.

This is the algebra that makes the function field of a curve over a finite field a global
function field, so that the theory of `C(Λ)` and of the Hecke operators
(`Stacks.Adeles.GlobalFunctionField`) applies to it.

## Main definitions

* `Stacks.Drinfeld.ratFuncAlgebra` — the `k(X)`-algebra structure on `K` given by `X ↦ t`.

## Main results

* `Stacks.Drinfeld.exists_transcendental_of_trdeg_ne_zero` — a transcendental element exists.
* `Stacks.Drinfeld.functionField_of_trdeg_eq_one` — `K` is finite over `k(X)`.
* `Stacks.Drinfeld.exists_algebra_functionField_fg_trdeg` — the function field of an integral
  scheme of dimension one, locally of finite type and universally closed over `k`, is finitely
  generated of transcendence degree one over `k`.
* `Stacks.Drinfeld.exists_functionField_of_isCurve` — the function field of a proper curve is a
  function field in the sense of `FunctionField`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Stacks.Drinfeld

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A field extension of nonzero transcendence degree has a transcendental element. -/
theorem exists_transcendental_of_trdeg_ne_zero (h : Algebra.trdeg k K ≠ 0) :
    ∃ t : K, Transcendental k t :=
  ((trdeg_ne_zero_iff).1 h).transcendental

/-- `X ↦ t` maps the nonzero polynomials to nonzero elements of `K` when `t` is
transcendental. -/
theorem nonZeroDivisors_le_comap_aeval {t : K} (ht : Transcendental k t) :
    nonZeroDivisors k[X] ≤ (nonZeroDivisors K).comap (aeval t : k[X] →ₐ[k] K) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    ((transcendental_iff_injective).1 ht)

/-- The `k(X)`-algebra structure on `K` given by `X ↦ t`, for `t` transcendental. -/
abbrev ratFuncAlgebra {t : K} (ht : Transcendental k t) : Algebra (RatFunc k) K :=
  (RatFunc.liftAlgHom (aeval t) (nonZeroDivisors_le_comap_aeval ht)).toRingHom.toAlgebra

/-- The algebra map of `ratFuncAlgebra` is the lift of `X ↦ t` to `k(X)`. -/
theorem ratFuncAlgebra_algebraMap {t : K} (ht : Transcendental k t) (f : RatFunc k) :
    @algebraMap (RatFunc k) K _ _ (ratFuncAlgebra ht) f =
      RatFunc.liftAlgHom (aeval t) (nonZeroDivisors_le_comap_aeval ht) f := rfl

/-- The `k(X)`-algebra structure `ratFuncAlgebra` on `K` is compatible with the `k`-algebra
structure. -/
theorem isScalarTower_ratFuncAlgebra {t : K} (ht : Transcendental k t) :
    letI := ratFuncAlgebra ht
    IsScalarTower k (RatFunc k) K := by
  let := ratFuncAlgebra ht
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [ratFuncAlgebra_algebraMap, AlgHom.commutes]

/-- **A finitely generated field extension of transcendence degree one is a function field.**
For `t ∈ K` transcendental over `k`, `K` is finite over `k(X)` embedded by `X ↦ t`. -/
theorem functionField_of_trdeg_eq_one (hfg : (⊤ : IntermediateField k K).FG)
    (htr : Algebra.trdeg k K = 1) {t : K} (ht : Transcendental k t) :
    letI := ratFuncAlgebra ht
    FunctionField k K := by
  let := ratFuncAlgebra ht
  let : Algebra k[X] K := (aeval t : k[X] →ₐ[k] K).toRingHom.toAlgebra
  have hpoly : ∀ p : k[X], algebraMap k[X] K p = aeval t p := fun _ => rfl
  have : IsScalarTower k k[X] K := IsScalarTower.of_algebraMap_eq fun c => by
    rw [hpoly, Polynomial.algebraMap_apply, aeval_C]; rfl
  have : IsScalarTower k[X] (RatFunc k) K := IsScalarTower.of_algebraMap_eq fun p => by
    rw [hpoly, ratFuncAlgebra_algebraMap, ← div_one (algebraMap k[X] (RatFunc k) p),
      ← map_one (algebraMap k[X] (RatFunc k)), RatFunc.liftAlgHom_apply_div, map_one, div_one]
  have : FaithfulSMul k[X] K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 ((transcendental_iff_injective).1 ht)
  have hadd := trdeg_add_eq k k[X] (A := K)
  rw [Polynomial.trdeg_of_isDomain, htr] at hadd
  have h0 : Algebra.trdeg k[X] K = 0 := by
    by_contra hne
    have h1 : 1 ≤ Algebra.trdeg k[X] K := Cardinal.one_le_iff_ne_zero.2 hne
    have : (1 : Cardinal) + 1 ≤ 1 := by
      have h2 := add_le_add (le_refl (1 : Cardinal)) h1
      rwa [hadd] at h2
    norm_num at this
  have halg : Algebra.IsAlgebraic k[X] K := (trdeg_eq_zero_iff).1 h0
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) :=
    IsFractionRing.injective k[X] (RatFunc k)
  obtain ⟨S, hS⟩ := hfg
  have htop : IntermediateField.adjoin (RatFunc k) (S : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ IntermediateField.adjoin k (S : Set K) := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin k (S : Set K) ≤
        (IntermediateField.adjoin (RatFunc k) (S : Set K)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin (RatFunc k) _)
    exact hle hx
  have hint : ∀ x ∈ (S : Set K), IsIntegral (RatFunc k) x := fun x _ =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := k[X]) x).extendScalars hinj).isIntegral
  have := IntermediateField.finiteDimensional_adjoin hint
  rw [htop] at this
  exact (IntermediateField.topEquiv (F := RatFunc k) (E := K)).toLinearEquiv.finiteDimensional


section Scheme

open AlgebraicGeometry CategoryTheory

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section IsIntegral

variable [IsIntegral X]

include f in
/-- A scheme over a field is surjective onto the point `Spec k`. -/
theorem surjective_toSpecField : Function.Surjective f := fun _ =>
  ⟨genericPoint X, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩

/-- **The function field of a curve has transcendence degree one and is finitely generated.**
Let `X` be an integral scheme, locally of finite type and universally closed over a field `k`,
of dimension one. For the `k`-algebra structure through an affine open `V`, the function field
`k(X)` is a finitely generated field extension of `k` of transcendence degree one. -/
theorem exists_algebra_functionField_fg_trdeg [LocallyOfFiniteType f] [UniversallyClosed f]
    (hX : topologicalKrullDim X = 1) :
    ∃ _ : Algebra k X.functionField, (⊤ : IntermediateField k X.functionField).FG ∧
      Algebra.trdeg k X.functionField = 1 := by
  classical
  have : AlgebraicGeometry.Surjective f := ⟨surjective_toSpecField f⟩
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := ⊤) trivial
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : Nonempty (⊤ : (Spec (.of k)).Opens) := ⟨⟨f (genericPoint X), trivial⟩⟩
  let A₀ := Γ(Spec (.of k), ⊤)
  let B := Γ(X, V)
  let K := X.functionField
  let e : k →+* A₀ := (Scheme.ΓSpecIso (.of k)).inv.hom
  have he : Function.Bijective e :=
    ((Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv).bijective
  let φ : A₀ →+* B := (f.appLE ⊤ V le_top).hom
  let : Algebra k A₀ := e.toAlgebra
  let : Algebra A₀ B := φ.toAlgebra
  let : Algebra k B := (φ.comp e).toAlgebra
  let : Algebra B K := (X.germToFunctionField V).hom.toAlgebra
  let : Algebra k K := ((algebraMap B K).comp (φ.comp e)).toAlgebra
  have : IsScalarTower k A₀ B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing B K := functionField_isFractionRing_of_isAffineOpen X V hV
  have hinj := ((tfae_isDominant_of_isIntegral f).out 1 4).mp (inferInstance : IsDominant f)
  have : FaithfulSMul A₀ B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (hinj ⟨V, hV⟩ ⟨⊤, isAffineOpen_top _⟩ inferInstance inferInstance le_top)
  have hF : let := f.functionFieldMap.hom.toAlgebra
      Algebra.trdeg (Spec (.of k)).functionField X.functionField = 1 := by
    let := f.functionFieldMap.hom.toAlgebra
    have h := topologicalKrullDim_eq_add_trdeg_of_isClosedMap f f.isClosedMap
    have h0 : topologicalKrullDim (Spec (.of k)) = 0 := by
      change topologicalKrullDim (PrimeSpectrum k) = _
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    rw [hX, h0, zero_add] at h
    have h1 : Cardinal.toENat (Algebra.trdeg (Spec (.of k)).functionField X.functionField) = 1 := by
      exact_mod_cast h.symm
    exact Cardinal.toENat_eq_one.1 h1
  have hAB : Algebra.trdeg A₀ B = 1 := by
    rw [← trdeg_functionField_eq_trdeg_appLE f (isAffineOpen_top _) hV le_top]
    exact hF
  have hkA : Algebra.trdeg k A₀ = 0 := by
    rw [trdeg_eq_zero_iff]
    refine ⟨fun a => ?_⟩
    obtain ⟨c, rfl⟩ := he.2 a
    exact isAlgebraic_algebraMap c
  have hkB : Algebra.trdeg k B = 1 := by
    rw [← trdeg_add_eq k A₀ (A := B), hkA, hAB, zero_add]
  have hBK : Algebra.trdeg B K = 0 :=
    (trdeg_eq_zero_iff).2 (IsLocalization.isAlgebraic K (nonZeroDivisors B))
  refine ⟨inferInstance, ?_, ?_⟩
  · have hft : φ.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩
        ⟨V, hV⟩ le_top
    obtain ⟨s, hs⟩ := hft.out
    refine ⟨s.image (algebraMap B K), ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hmem : ∀ c : B, algebraMap B K c ∈
        IntermediateField.adjoin k ((s.image (algebraMap B K) : Finset K) : Set K) := by
      intro c
      have hc : c ∈ Algebra.adjoin A₀ (s : Set B) := hs ▸ Algebra.mem_top
      induction hc using Algebra.adjoin_induction with
      | mem y hy =>
        exact IntermediateField.subset_adjoin k _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))
      | algebraMap r =>
        obtain ⟨c', rfl⟩ := he.2 r
        exact IntermediateField.algebraMap_mem _ c'
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
    exact div_mem (hmem a) (hmem b)
  · rw [← trdeg_add_eq k B (A := K), hkB, hBK, add_zero]

end IsIntegral

/-- **The function field of a proper curve over `k` is a function field over `k`**: it carries a
`k`-algebra and a `k(X)`-algebra structure for which it is a finite extension of `k(X)`. -/
theorem exists_functionField_of_isCurve [IsCurve k f] [IsProper f] :
    ∃ (_ : Algebra k X.functionField) (_ : Algebra (RatFunc k) X.functionField)
      (_ : IsScalarTower k (RatFunc k) X.functionField), FunctionField k X.functionField := by
  obtain ⟨_, hfg, htr⟩ := exists_algebra_functionField_fg_trdeg f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))
  obtain ⟨t, ht⟩ := exists_transcendental_of_trdeg_ne_zero (k := k) (K := X.functionField)
    (by rw [htr]; exact one_ne_zero)
  exact ⟨_, ratFuncAlgebra ht, isScalarTower_ratFuncAlgebra ht,
    functionField_of_trdeg_eq_one hfg htr ht⟩

end Scheme

end Stacks.Drinfeld

end
