module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import StacksFrontier.KTheory.Grothendieck.Artinian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Length over a local ring of a module over a semi-local algebra

Let `A` be a commutative local ring with maximal ideal `𝔪`, and let `B` be an `A`-algebra along
`f = algebraMap A B`. Suppose `B` is semi-local, its maximal ideals being exactly the members of
a family `𝔪 : Fin n → Ideal B`, and assume that

* every `𝔪 i` lies over `𝔪`, that is `IsLocalRing.maximalIdeal A = (𝔪 i).comap f`; and
* every residue degree `[κ(𝔪 i) : κ(𝔪)]` is finite.

Then a `B`-module `M` of finite length over `B` has finite length over `A`, and

  `Module.length A M = ∑_{i} [κ(𝔪 i) : κ(𝔪)] · length_{B_{𝔪 i}}(M_{𝔪 i})`,

the sum being taken in `ℕ∞` with the factor `[κ(𝔪 i) : κ(𝔪)]` the natural number
`Module.finrank κ(𝔪) κ(𝔪 i)` coerced into `ℕ∞`. Here `M` is regarded as an `A`-module by
restriction of scalars along `f`, encoded by `[Module A M]` together with
`[IsScalarTower A B M]`.

## Main definitions

* `residueFieldAlgebra`: the `κ(𝔪)`-algebra structure on `κ(𝔪 i)` induced by `f`.

## Main results

* `length_simple_quotient_eq`: the length formula for a simple `B`-module.
* `length_eq_sum_residue_degree_mul_localized_length`: the length formula in general.
-/

@[expose] public section

open IsLocalRing

/-- The `κ(𝔪)`-algebra structure on the residue field `κ(𝔪 i)`, induced by the
ring homomorphism `f = algebraMap A B` via the "lies over" relation
`𝔪 = (𝔪 i).comap f`. Concretely, `f` induces a field homomorphism
`κ(𝔪) → κ(𝔪 i)` (using `Ideal.ResidueField.map`), and this is the algebra
structure with respect to which the residue degree `[κ(𝔪 i) : κ(𝔪)]` is
computed. -/
@[reducible, ega "0 1.0.7"]
noncomputable def residueFieldAlgebra {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] (𝔪i : Ideal B) [𝔪i.IsMaximal]
    (h : IsLocalRing.maximalIdeal A = 𝔪i.comap (algebraMap A B)) :
    Algebra (IsLocalRing.maximalIdeal A).ResidueField 𝔪i.ResidueField :=
  (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) 𝔪i (algebraMap A B) h).toAlgebra

/-- Let `B` be semi-local with maximal ideals exactly `𝔪 0, …, 𝔪 (n-1)`, each lying over the
maximal ideal of the local ring `A` and of finite residue degree. A simple `B`-module `S` then
has finite `A`-length, and

  `length_A S = ∑ i, [κ(𝔪 i) : κ(𝔪_A)] · length_{B_{𝔪 i}}(S_{𝔪 i})`.

The sum has a single nonzero term, at the index `j` with `𝔪 j` the annihilator of `S`. -/
theorem length_simple_quotient_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    {S : Type*} [AddCommGroup S] [Module B S] [Module A S] [IsScalarTower A B S]
    (n : ℕ) (𝔪 : Fin n → Ideal B)
    (hmax : ∀ i, (𝔪 i).IsMaximal)
    (hinj : Function.Injective 𝔪)
    (hsurj : ∀ I : Ideal B, I.IsMaximal → ∃ i, 𝔪 i = I)
    (hlies : ∀ i, IsLocalRing.maximalIdeal A = (𝔪 i).comap (algebraMap A B))
    (hS : IsSimpleModule B S) :
    letI : ∀ i, (𝔪 i).IsMaximal := hmax
    letI : ∀ i, Algebra (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField :=
      fun i => residueFieldAlgebra (𝔪 i) (hlies i)
    (∀ i, Module.Finite (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField) →
      IsFiniteLength A S ∧
        Module.length A S
          = ∑ i : Fin n,
              (Module.finrank (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField : ℕ∞)
                * Module.length (Localization.AtPrime (𝔪 i))
                    (LocalizedModule (𝔪 i).primeCompl S) := by
  let : ∀ i, (𝔪 i).IsMaximal := hmax
  let algRes : ∀ i, Algebra (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField :=
    fun i => residueFieldAlgebra (𝔪 i) (hlies i)
  intro hfin
  -- (a) identify the unique `j` with `𝔪 j = annihilator B S`, and `S ≃ₗ[B] κ(𝔪 j)`.
  have hannmax : (Module.annihilator B S).IsMaximal := IsSimpleModule.annihilator_isMaximal
  obtain ⟨j, hj⟩ := hsurj (Module.annihilator B S) hannmax
  -- `S ≃ₗ[B] B ⧸ I` for a maximal `I`; then `I = annihilator = 𝔪 j`.
  obtain ⟨I, hImax, ⟨eQ⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
  have hIann : I = Module.annihilator B S := by
    have h := eQ.annihilator_eq
    rw [Ideal.annihilator_quotient] at h
    exact h.symm
  have hIj : I = 𝔪 j := by rw [hIann, ← hj]
  -- `B ⧸ 𝔪 j ≃ₗ[B] κ(𝔪 j)`.
  have : (𝔪 j).IsMaximal := hmax j
  have eRF : (B ⧸ 𝔪 j) ≃ₗ[B] (𝔪 j).ResidueField := by
    have hsurjR : Function.Surjective (Algebra.linearMap B (𝔪 j).ResidueField) :=
      Ideal.algebraMap_residueField_surjective (𝔪 j)
    have hker : LinearMap.ker (Algebra.linearMap B (𝔪 j).ResidueField) = 𝔪 j := by
      ext x
      simp only [LinearMap.mem_ker, Algebra.linearMap_apply,
        Ideal.algebraMap_residueField_eq_zero]
    exact (Submodule.quotEquivOfEq (𝔪 j) _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective _ hsurjR)
  -- the central `B`-linear equivalence `S ≃ₗ[B] κ(𝔪 j)`.
  have eB : S ≃ₗ[B] (𝔪 j).ResidueField :=
    (eQ.trans (Submodule.quotEquivOfEq I (𝔪 j) hIj)).trans eRF
  -- (b) `length_A S = finrank κ(𝔪_A) κ(𝔪 j)`, finite.
  -- scalar tower `A → κ(𝔪_A) → κ(𝔪 j)`.
  have hst : IsScalarTower A (IsLocalRing.maximalIdeal A).ResidueField (𝔪 j).ResidueField := by
    have hcomp : ∀ a : A,
        (algebraMap (IsLocalRing.maximalIdeal A).ResidueField (𝔪 j).ResidueField)
          (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a)
            = algebraMap A (𝔪 j).ResidueField a := by
      intro a
      show (Ideal.ResidueField.map (IsLocalRing.maximalIdeal A) (𝔪 j)
          (algebraMap A B) (hlies j))
          (algebraMap A (IsLocalRing.maximalIdeal A).ResidueField a) = _
      rw [Ideal.ResidueField.map_algebraMap]; rfl
    refine ⟨fun a x y => ?_⟩
    simp only [Algebra.smul_def]
    rw [map_mul, hcomp, mul_assoc]
  have hlenA : Module.length A S
      = (Module.finrank (IsLocalRing.maximalIdeal A).ResidueField (𝔪 j).ResidueField : ℕ∞) := by
    have hAeq : Module.length A S = Module.length A (𝔪 j).ResidueField :=
      (eB.restrictScalars A).length_eq
    rw [hAeq,
      Module.length_eq_of_surjective (S := A) (R := (IsLocalRing.maximalIdeal A).ResidueField)
        (M := (𝔪 j).ResidueField) (Ideal.algebraMap_residueField_surjective _)]
    exact Module.length_eq_finrank _ _
  have hFinA : IsFiniteLength A S := by
    rw [← Module.length_ne_top_iff, hlenA]
    exact ENat.natCast_ne_top _
  refine ⟨hFinA, ?_⟩
  -- (c) collapse the RHS sum to the `j`-term.
  rw [hlenA]
  rw [Finset.sum_eq_single j]
  · -- the `j`-term equals `finrank κ(𝔪_A) κ(𝔪 j)`.
    have hlocj : Module.length (Localization.AtPrime (𝔪 j))
        (LocalizedModule (𝔪 j).primeCompl S) = 1 := by
      -- `LocalizedModule primeCompl S ≃ₗ[Loc] κ(𝔪 j)`, which is `Loc`-simple.
      let : Module (Localization.AtPrime (𝔪 j)) (𝔪 j).ResidueField := inferInstance
      -- `κ(𝔪 j)` as localized module of itself.
      have hidloc : IsLocalizedModule (𝔪 j).primeCompl
          (LinearMap.id : (𝔪 j).ResidueField →ₗ[B] (𝔪 j).ResidueField) :=
        isLocalizedModule_id (𝔪 j).primeCompl (𝔪 j).ResidueField (Localization.AtPrime (𝔪 j))
      -- `LocalizedModule primeCompl κ(𝔪 j) ≃ₗ[B] κ(𝔪 j)`, upgraded to `Loc`-linear.
      have e1B : LocalizedModule (𝔪 j).primeCompl (𝔪 j).ResidueField ≃ₗ[B] (𝔪 j).ResidueField :=
        IsLocalizedModule.iso (𝔪 j).primeCompl LinearMap.id
      have e1 : LocalizedModule (𝔪 j).primeCompl (𝔪 j).ResidueField
          ≃ₗ[Localization.AtPrime (𝔪 j)] (𝔪 j).ResidueField :=
        LinearEquiv.extendScalarsOfIsLocalization (𝔪 j).primeCompl
          (Localization.AtPrime (𝔪 j)) e1B
      -- `LocalizedModule primeCompl S ≃ₗ[Loc] LocalizedModule primeCompl κ(𝔪 j)`.
      have e2 : LocalizedModule (𝔪 j).primeCompl S
          ≃ₗ[Localization.AtPrime (𝔪 j)] LocalizedModule (𝔪 j).primeCompl (𝔪 j).ResidueField :=
        LinearEquiv.ofBijective (LocalizedModule.map (𝔪 j).primeCompl (eB : S →ₗ[B] _))
          ⟨IsLocalizedModule.map_injective _ _ _ _ eB.injective,
            IsLocalizedModule.map_surjective _ _ _ _ eB.surjective⟩
      have eLoc : LocalizedModule (𝔪 j).primeCompl S
          ≃ₗ[Localization.AtPrime (𝔪 j)] (𝔪 j).ResidueField := e2.trans e1
      have : IsSimpleModule (Localization.AtPrime (𝔪 j)) (𝔪 j).ResidueField :=
        isSimpleModule_residueField (Localization.AtPrime (𝔪 j))
      exact Module.length_eq_one_iff.mpr (IsSimpleModule.congr eLoc)
    rw [hlocj, mul_one]
  · -- terms `i ≠ j` vanish: `S_{𝔪 i} = 0`.
    intro i _ hij
    have hne : 𝔪 i ≠ 𝔪 j := fun h => hij (hinj h)
    -- find `t ∈ (𝔪 i).primeCompl` annihilating `S`.
    have hnotle : ¬ ((𝔪 j) : Set B) ⊆ 𝔪 i := by
      intro hle
      exact hne ((hmax j).eq_of_le (hmax i).ne_top hle).symm
    rw [Set.not_subset] at hnotle
    obtain ⟨t, htJ, htI⟩ := hnotle
    have hannt : ∀ m : S, t • m = 0 := by
      have : t ∈ Module.annihilator B S := hj ▸ htJ
      exact Module.mem_annihilator.mp this
    have hsub : Subsingleton (LocalizedModule (𝔪 i).primeCompl S) := by
      constructor
      intro a b
      induction a using LocalizedModule.induction_on with
      | _ m u =>
        induction b using LocalizedModule.induction_on with
        | _ m' u' =>
          rw [LocalizedModule.mk_eq]
          refine ⟨⟨t, htI⟩, ?_⟩
          have h1 : (⟨t, htI⟩ : (𝔪 i).primeCompl) • u' • m = u' • (t • m) := by
            rw [Submonoid.smul_def, smul_comm]
          have h2 : (⟨t, htI⟩ : (𝔪 i).primeCompl) • u • m' = u • (t • m') := by
            rw [Submonoid.smul_def, smul_comm]
          rw [h1, h2, hannt m, hannt m', smul_zero, smul_zero]
    rw [Module.length_eq_zero_iff.mpr hsub, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Stacks 02M0.** Length over a local ring `A` of a finite-length module
`M` over a semi-local `A`-algebra `B`, expressed as a sum over the (finitely
many) maximal ideals of `B` of the residue degrees times the lengths of the
localizations. -/
@[stacks 02M0, ega "IV 21.10.11" "partial", sga "3 VIIB 1.2.6" "partial"]
theorem length_eq_sum_residue_degree_mul_localized_length
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (n : ℕ) (𝔪 : Fin n → Ideal B)
    -- `B` is semi-local with the `𝔪 i` being exactly its maximal ideals:
    (hmax : ∀ i, (𝔪 i).IsMaximal)
    (hinj : Function.Injective 𝔪)
    (hsurj : ∀ I : Ideal B, I.IsMaximal → ∃ i, 𝔪 i = I)
    -- each `𝔪 i` lies over the maximal ideal of `A`:
    (hlies : ∀ i, IsLocalRing.maximalIdeal A = (𝔪 i).comap (algebraMap A B))
    -- `M` has finite length over `B`:
    (hM : IsFiniteLength B M) :
    -- introduce the residue-field algebra structures and the primality of the `𝔪 i`:
    letI : ∀ i, (𝔪 i).IsMaximal := hmax
    letI : ∀ i, Algebra (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField :=
      fun i => residueFieldAlgebra (𝔪 i) (hlies i)
    -- finiteness of residue degrees `[κ(𝔪 i) : κ(𝔪)] < ∞`:
    (∀ i, Module.Finite (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField) →
      -- `M` has finite length over `A`, and the length formula holds in `ℕ∞`:
      IsFiniteLength A M ∧
        Module.length A M
          = ∑ i : Fin n,
              (Module.finrank (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField : ℕ∞)
                * Module.length (Localization.AtPrime (𝔪 i))
                    (LocalizedModule (𝔪 i).primeCompl M) := by
  let : ∀ i, (𝔪 i).IsMaximal := hmax
  let algRes : ∀ i, Algebra (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField :=
    fun i => residueFieldAlgebra (𝔪 i) (hlies i)
  intro hfin
  -- We prove a generalized statement for all finite-length `B`-modules, by induction
  -- on `IsFiniteLength B`.  The `A`-module structure is supplied explicitly inside the
  -- motive so the induction can carry it along.
  suffices H : ∀ (X : Type _) [AddCommGroup X] [Module B X], IsFiniteLength B X →
      ∀ [Module A X] [IsScalarTower A B X],
        IsFiniteLength A X ∧
          Module.length A X =
            ∑ i : Fin n,
              (Module.finrank (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField : ℕ∞)
                * Module.length (Localization.AtPrime (𝔪 i))
                    (LocalizedModule (𝔪 i).primeCompl X) by
    exact H M hM
  clear hM
  intro X _ _ hX
  induction hX with
  | @of_subsingleton X _ _ _ =>
      intro _ _
      refine ⟨IsFiniteLength.of_subsingleton, ?_⟩
      have hLHS : Module.length A X = 0 := Module.length_eq_zero_iff.mpr inferInstance
      rw [hLHS]
      symm
      apply Finset.sum_eq_zero
      intro i _
      have : Subsingleton (LocalizedModule (𝔪 i).primeCompl X) := inferInstance
      rw [Module.length_eq_zero_iff.mpr this, mul_zero]
  | @of_simple_quotient X _ _ N _ hN ih =>
      intro _ _
      obtain ⟨ihFin, ihEq⟩ := ih
      -- The formula for the simple `B`-module quotient `X ⧸ N`.
      have hQ : IsFiniteLength A (X ⧸ N) ∧
          Module.length A (X ⧸ N) =
            ∑ i : Fin n,
              (Module.finrank (IsLocalRing.maximalIdeal A).ResidueField (𝔪 i).ResidueField : ℕ∞)
                * Module.length (Localization.AtPrime (𝔪 i))
                    (LocalizedModule (𝔪 i).primeCompl (X ⧸ N)) :=
        length_simple_quotient_eq n 𝔪 hmax hinj hsurj hlies inferInstance hfin
      obtain ⟨hQFin, hQEq⟩ := hQ
      -- A-side additivity along `0 → N → X → X⧸N → 0`:
      have hAadd : Module.length A X = Module.length A ↥N + Module.length A (X ⧸ N) :=
        Module.length_eq_add_of_exact ((N.subtype).restrictScalars A)
          ((N.mkQ).restrictScalars A) (Submodule.injective_subtype N)
          (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
      -- localization-side additivity, for each `i`:
      have hLoc : ∀ i : Fin n,
          Module.length (Localization.AtPrime (𝔪 i)) (LocalizedModule (𝔪 i).primeCompl X)
            = Module.length (Localization.AtPrime (𝔪 i)) (LocalizedModule (𝔪 i).primeCompl ↥N)
              + Module.length (Localization.AtPrime (𝔪 i))
                  (LocalizedModule (𝔪 i).primeCompl (X ⧸ N)) := by
        intro i
        set S := (𝔪 i).primeCompl
        have hinjL : Function.Injective ⇑(LocalizedModule.map S N.subtype) :=
          IsLocalizedModule.map_injective _ _ _ _ (Submodule.injective_subtype N)
        have hsurjL : Function.Surjective ⇑(LocalizedModule.map S N.mkQ) :=
          IsLocalizedModule.map_surjective _ _ _ _ (Submodule.mkQ_surjective N)
        have hexL : Function.Exact ⇑(LocalizedModule.map S N.subtype)
            ⇑(LocalizedModule.map S N.mkQ) :=
          LocalizedModule.map_exact S N.subtype N.mkQ (LinearMap.exact_subtype_mkQ N)
        exact Module.length_eq_add_of_exact (LocalizedModule.map S N.subtype)
          (LocalizedModule.map S N.mkQ) hinjL hsurjL hexL
      refine ⟨?_, ?_⟩
      · -- finiteness over A
        rw [← Module.length_ne_top_iff] at ihFin hQFin ⊢
        rw [hAadd]
        exact WithTop.add_ne_top.mpr ⟨ihFin, hQFin⟩
      · -- length formula
        rw [hAadd, ihEq, hQEq]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hLoc i, mul_add]
