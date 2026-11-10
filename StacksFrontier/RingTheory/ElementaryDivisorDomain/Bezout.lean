module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Valuation.Generalized

/-!
# Modules over a Bézout domain

Localizations of a Bézout domain are again Bézout, so the local rings of a Bézout domain are
valuation rings; conversely a local domain is Bézout exactly when it is a valuation ring. Over a
Bézout domain every finitely generated submodule of a free module is finite free, and every
finitely presented module is the direct sum of a finite free module and its torsion submodule,
the latter being a direct summand of a finite direct sum of cyclic modules `R ⧸ (f)` with
`f ≠ 0`.

## Main results

* `isBezout_localization_and_valuationRing_atPrime_and_iff`: localizations of a Bézout domain are
  Bézout, its local rings are valuation rings, and a local domain is Bézout exactly when it is a
  valuation ring.
* `finite_submodule_free_and_finitePresentation_split_torsion`: over a Bézout domain, finite
  submodules of free modules are free, and a finitely presented module splits as the direct sum of
  its finite free torsion quotient and its torsion submodule.

## References

* [Stacks, Tag 0AST](https://stacks.math.columbia.edu/tag/0AST)
* [Stacks, Tag 0ASU](https://stacks.math.columbia.edu/tag/0ASU)
-/

@[expose] public section

open scoped DirectSum

universe u v w

/-! ### Localizations of a Bézout domain -/

private theorem isBezout_of_isLocalization
    {R S : Type*} [CommRing R] [IsBezout R] (M : Submonoid R)
    [CommRing S] [Algebra R S] [IsLocalization M S] : IsBezout S := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨a, b, d, ha, hb⟩ := IsLocalization.surj₂ M S x y
  have hd : IsUnit (algebraMap R S d) := IsLocalization.map_units S d
  obtain ⟨g, hg⟩ := (IsBezout.span_pair_isPrincipal a b).1
  refine ⟨⟨algebraMap R S g, ?_⟩⟩
  rw [Ideal.span_insert, ← Ideal.span_singleton_mul_right_unit hd x,
    ← Ideal.span_singleton_mul_right_unit hd y, ha, hb]
  calc
    Ideal.span {(algebraMap R S) a} ⊔ Ideal.span {(algebraMap R S) b} =
        Ideal.map (algebraMap R S) (Ideal.span {a} ⊔ Ideal.span {b}) := by
          rw [Ideal.map_sup]
          simp [Ideal.map_span]
    _ = Ideal.map (algebraMap R S) (Ideal.span {a, b}) := by rw [Ideal.span_insert]
    _ = Ideal.map (algebraMap R S) (Ideal.span {g}) := by rw [hg]
    _ = Ideal.span {(algebraMap R S) g} := by simp [Ideal.map_span]

/-- Localizations of a Bézout domain are Bézout, its local rings are valuation rings, and an
arbitrary local domain is Bézout if and only if it is a valuation ring. -/
@[stacks 0AST]
theorem isBezout_localization_and_valuationRing_atPrime_and_iff
    {R Rₘ A : Type*} [CommRing R] [IsDomain R] [IsBezout R]
    (M : Submonoid R) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ]
    (p : Ideal R) [p.IsPrime]
    [CommRing A] [IsDomain A] [IsLocalRing A] :
    IsBezout Rₘ ∧
      ValuationRing (Localization.AtPrime p) ∧
      (IsBezout A ↔ ValuationRing A) := by
  let : IsBezout Rₘ := isBezout_of_isLocalization M
  let : IsBezout (Localization.AtPrime p) := isBezout_of_isLocalization p.primeCompl
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ValuationRing.iff_local_bezout_domain]
  exact ⟨fun h ↦ ⟨inferInstance, h⟩, And.right⟩

/-! ### Splitting off the free part over a Bézout domain -/

private theorem ideal_free (R : Type u) [CommRing R] [IsDomain R] [IsBezout R]
    (I : Ideal R) [Module.Finite R I] : Module.Free R I := by
  classical
  have : I.IsPrincipal := IsBezout.isPrincipal_of_FG I (Submodule.FG.of_finite)
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  · exact Module.Free.of_equiv (Ideal.isoBaseOfIsPrincipal hI)

private theorem finite_ker_of_finite_projective (R : Type u) [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] (f : M →ₗ[R] P) (hf : Function.Surjective f) :
    Module.Finite R f.ker := by
  let : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  exact Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)

/-- If finite submodules of `P` are free and `P ≃ₗ Q`, then finite submodules of `Q` are free. -/
private theorem free_submodule_of_equiv (R : Type*) [CommRing R]
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] (e : P ≃ₗ[R] Q)
    (h : ∀ (K : Submodule R P), [Module.Finite R K] → Module.Free R K)
    (K : Submodule R Q) [Module.Finite R K] : Module.Free R K := by
  let : Module.Finite R (K.map e.symm.toLinearMap) := Module.Finite.map K e.symm.toLinearMap
  have := h (K.map e.symm.toLinearMap)
  exact Module.Free.of_equiv (e.symm.submoduleMap K).symm

/-- A finite module injecting into `F` is free if finite submodules of `F` are free. -/
private theorem free_of_injective (R : Type*) [CommRing R] {Q F : Type*}
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [AddCommGroup F] [Module R F]
    (hF : ∀ (K : Submodule R F), [Module.Finite R K] → Module.Free R K)
    (f : Q →ₗ[R] F) (hf : Function.Injective f) : Module.Free R Q := by
  let : Module.Finite R f.range := Module.Finite.range f
  let : Module.Free R f.range := hF f.range
  exact Module.Free.of_equiv (LinearEquiv.ofInjective f hf).symm

/-- A map `q : M → Q` with a section `s` identifies `M` with `Q × T`, where `T` is the kernel. -/
private theorem nonempty_equiv_prod_of_section (R : Type*) [CommRing R]
    {M Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (q : M →ₗ[R] Q) (T : Submodule R M) (hT : ∀ x, q x = 0 ↔ x ∈ T)
    (s : Q →ₗ[R] M) (hs : ∀ y, q (s y) = y) : Nonempty (M ≃ₗ[R] Q × T) := by
  let t : M →ₗ[R] T := LinearMap.codRestrict T (LinearMap.id - s.comp q) (by
    intro x
    simp [← hT, hs])
  refine ⟨LinearEquiv.ofBijective (q.prod t) ⟨fun x y hxy => ?_, ?_⟩⟩
  · have hsub : x - s (q x) = y - s (q y) := congrArg Subtype.val (congrArg Prod.snd hxy)
    rw [show q x = q y from congrArg Prod.fst hxy] at hsub
    simpa only [sub_left_inj] using hsub
  · rintro ⟨a, z⟩
    have hz : q z.1 = 0 := (hT _).mpr z.2
    refine ⟨s a + z.1, Prod.ext ?_ (Subtype.ext ?_)⟩
    · simp [hs, hz]
    · simp [hs, hz, t]

private theorem free_finite_submodule_prod (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) (P : Type w) [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P]
    (hM : ∀ (K : Submodule R M), [Module.Finite R K] → Module.Free R K)
    (hP : ∀ (K : Submodule R P), [Module.Finite R K] → Module.Free R K)
    (N : Submodule R (M × P)) [Module.Finite R N] : Module.Free R N := by
  classical
  let I : Submodule R P := Submodule.map (LinearMap.snd R M P) N
  let q : N →ₗ[R] I := (LinearMap.snd R M P).submoduleMap N
  have hq : Function.Surjective q := LinearMap.submoduleMap_surjective _ _
  let : Module.Finite R I := Module.Finite.map N (LinearMap.snd R M P)
  let : Module.Free R I := hP I
  let : Module.Finite R q.ker := finite_ker_of_finite_projective R q hq
  let t : q.ker →ₗ[R] M := (LinearMap.fst R M P).comp
    (N.subtype.comp q.ker.subtype)
  have ht : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hxy
    · have hx : ((x.1.1 : M × P).2) = 0 := congrArg Subtype.val x.2
      have hy : ((y.1.1 : M × P).2) = 0 := congrArg Subtype.val y.2
      exact hx.trans hy.symm
  let : Module.Free R q.ker := free_of_injective R hM t ht
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  obtain ⟨e⟩ := nonempty_equiv_prod_of_section R q q.ker (fun _ => LinearMap.mem_ker) s
    (LinearMap.congr_fun hs)
  exact Module.Free.of_equiv e.symm

private theorem free_finite_submodule_pi (R : Type u) [CommRing R] [IsDomain R]
    [IsBezout R] (ι : Type v) [Finite ι]
    (N : Submodule R (ι → R)) [Module.Finite R N] : Module.Free R N := by
  classical
  let motive : ∀ (P : Type u) [AddCommGroup P] [Module R P], Prop :=
    fun P _ _ => ∀ (K : Submodule R P), [Module.Finite R K] → Module.Free R K
  let motive' : ∀ (P : Type (max u v)) [AddCommGroup P] [Module R P], Prop :=
    fun P _ _ => ∀ (K : Submodule R P), [Module.Finite R K] → Module.Free R K
  have hunit : motive PUnit := fun K _ => inferInstance
  have hprod : ∀ {P : Type u} {Q : Type (max u v)} [AddCommGroup P]
      [AddCommGroup Q] [Module R P] [Module R Q],
      motive P → motive' Q → motive' (P × Q) := by
    intro P Q _ _ _ _ hP hQ K _
    exact free_finite_submodule_prod R P Q hP hQ K
  exact Module.pi_induction' R motive motive'
    (fun e h K _ => free_submodule_of_equiv R e h K)
    (fun e h K _ => free_submodule_of_equiv R e h K) hunit hprod
    (fun _ : ι => R) (fun _ => ideal_free R) N

private theorem free_finite_submodule_finsupp (R : Type u) [CommRing R] [IsDomain R]
    [IsBezout R] (ι : Type v) (N : Submodule R (ι →₀ R)) [Module.Finite R N] :
    Module.Free R N := by
  classical
  obtain ⟨S, hS, hspan⟩ := Submodule.fg_def.mp (Submodule.FG.of_finite (N := N))
  let t : Set ι := ⋃ x ∈ S, (x.support : Set ι)
  have ht : t.Finite := hS.biUnion fun x _ => x.support.finite_toSet
  let : Finite t := ht.to_subtype
  let U : Submodule R (ι →₀ R) := Finsupp.supported R R t
  have hle : N ≤ U := by
    rw [← hspan]
    exact Finsupp.span_le_supported_biUnion_support (R := R) S
  let J : Submodule R U := N.comap U.subtype
  let eJ : J ≃ₗ[R] N := Submodule.comapSubtypeEquivOfLe hle
  let : Module.Finite R J := Module.Finite.equiv eJ.symm
  let e : U ≃ₗ[R] t → R :=
    (Finsupp.supportedEquivFinsupp t).trans (Finsupp.linearEquivFunOnFinite R R t)
  let : Module.Free R J :=
    free_submodule_of_equiv R e.symm (fun K _ => free_finite_submodule_pi R t K) J
  exact Module.Free.of_equiv eJ

private theorem free_finite_submodule (R : Type u) [CommRing R] [IsDomain R]
    [IsBezout R] (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F]
    (N : Submodule R F) [Module.Finite R N] : Module.Free R N := by
  classical
  exact free_submodule_of_equiv R (Module.Free.chooseBasis R F).repr.symm
    (fun K _ => free_finite_submodule_finsupp R _ K) N

/-- The map `R ⧸ (f) → R` which is the canonical isomorphism when `f = 0` and zero otherwise. -/
private noncomputable def freePart (R : Type*) [CommRing R] [IsDomain R] (f : R) :
    (R ⧸ Ideal.span {f}) →ₗ[R] R := by
  classical
  exact if h : f = 0 then
    ((Ideal.quotientEquivAlgOfEq R (by simp [h])).trans
      (AlgEquiv.quotientBot R R)).toLinearEquiv.toLinearMap
  else 0

private theorem freePart_injective (R : Type*) [CommRing R] [IsDomain R] (f : R) (hf : f = 0) :
    Function.Injective (freePart R f) := by
  classical
  simpa [freePart, hf] using
    (((Ideal.quotientEquivAlgOfEq R (by simp [hf])).trans
      (AlgEquiv.quotientBot R R)).toLinearEquiv).injective

/-- `f` itself when `f ≠ 0`, and `1` otherwise. -/
private noncomputable def nonzeroPart (R : Type*) [CommRing R] [IsDomain R] (f : R) : R := by
  classical exact if f = 0 then 1 else f

private theorem nonzeroPart_ne_zero (R : Type*) [CommRing R] [IsDomain R] (f : R) :
    nonzeroPart R f ≠ 0 := by
  classical
  by_cases h : f = 0 <;> simp [nonzeroPart, h]

private noncomputable def toTorsion (R : Type*) [CommRing R] [IsDomain R] (f : R) :
    (R ⧸ Ideal.span {f}) →ₗ[R] R ⧸ Ideal.span {nonzeroPart R f} := by
  classical
  by_cases h : f = 0
  · exact 0
  · exact (Ideal.quotientEquivAlgOfEq R (by simp [nonzeroPart, h])).toLinearEquiv.toLinearMap

private noncomputable def fromTorsion (R : Type*) [CommRing R] [IsDomain R] (f : R) :
    (R ⧸ Ideal.span {nonzeroPart R f}) →ₗ[R] R ⧸ Ideal.span {f} := by
  classical
  by_cases h : f = 0
  · exact 0
  · exact (Ideal.quotientEquivAlgOfEq R (by simp [nonzeroPart, h])).toLinearEquiv.symm.toLinearMap

private theorem from_to_of_ne (R : Type*) [CommRing R] [IsDomain R] (f : R) (hf : f ≠ 0)
    (x : R ⧸ Ideal.span {f}) :
    fromTorsion R f (toTorsion R f x) = x := by
  classical
  let e : (R ⧸ Ideal.span {f}) ≃ₗ[R] (R ⧸ Ideal.span {nonzeroPart R f}) :=
    (Ideal.quotientEquivAlgOfEq R (by simp [nonzeroPart, hf])).toLinearEquiv
  simp only [fromTorsion, toTorsion, dite_eq_right hf]
  exact e.symm_apply_apply x

private theorem from_to_of_zero (R : Type*) [CommRing R] [IsDomain R] (f : R) (hf : f = 0)
    (x : R ⧸ Ideal.span {f}) :
    fromTorsion R f (toTorsion R f x) = 0 := by
  classical
  simp [fromTorsion, toTorsion, hf]

private theorem quotient_torsion (R : Type*) [CommRing R] [IsDomain R] (f : R) (hf : f ≠ 0)
    (x : R ⧸ Ideal.span {f}) : x ∈ Submodule.torsion R _ := by
  rw [Submodule.mem_torsion_iff]
  refine ⟨⟨f, mem_nonZeroDivisors_of_ne_zero hf⟩, ?_⟩
  induction x using Quotient.inductionOn' with
  | h a =>
    change f • (Ideal.Quotient.mk _ a) = 0
    change (Ideal.Quotient.mk _ f) * (Ideal.Quotient.mk _ a) = 0
    have hmem : f ∈ Ideal.span ({f} : Set R) := Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul]

private theorem torsion_of_map (R : Type*) [CommRing R] [IsDomain R]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (l : M →ₗ[R] N) {x : M}
    (hx : x ∈ Submodule.torsion R M) : l x ∈ Submodule.torsion R N := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  exact (Submodule.mem_torsion_iff _).mpr ⟨a, by simpa using congrArg l ha⟩

private theorem torsion_map_to_ring_zero (R : Type*) [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (l : M →ₗ[R] R) {x : M} (hx : x ∈ Submodule.torsion R M) : l x = 0 := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  have ha' : (a : R) • l x = 0 := by
    simpa only [Submonoid.smul_def, map_smul, map_zero] using congrArg l ha
  change (a : R) * l x = 0 at ha'
  exact (mul_eq_zero.mp ha').resolve_left (nonZeroDivisors.coe_ne_zero a)

private noncomputable def freeCoordinates (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (f : Fin n → R) :
    (⨁ j : Fin n, R ⧸ Ideal.span {f j}) →ₗ[R] (Fin n → R) :=
  (DirectSum.linearEquivFunOnFintype R (Fin n) (fun _ => R)).toLinearMap.comp
    (DirectSum.lmap fun j => freePart R (f j))

private noncomputable def toTorsionSum (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (f : Fin n → R) :
    (⨁ j : Fin n, R ⧸ Ideal.span {f j}) →ₗ[R]
      (⨁ j : Fin n, R ⧸ Ideal.span {nonzeroPart R (f j)}) :=
  DirectSum.lmap fun j => toTorsion R (f j)

private noncomputable def fromTorsionSum (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (f : Fin n → R) :
    (⨁ j : Fin n, R ⧸ Ideal.span {nonzeroPart R (f j)}) →ₗ[R]
      (⨁ j : Fin n, R ⧸ Ideal.span {f j}) :=
  DirectSum.lmap fun j => fromTorsion R (f j)

private theorem torsion_torsionSum (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) (f : Fin n → R)
    (b : ⨁ j : Fin n, R ⧸ Ideal.span {nonzeroPart R (f j)}) :
    b ∈ Submodule.torsion R _ := by
  classical
  induction b using DirectSum.induction_on with
  | zero => exact (Submodule.torsion R _).zero_mem
  | of j x =>
      exact torsion_of_map R (DirectSum.lof R (Fin n)
        (fun j => R ⧸ Ideal.span {nonzeroPart R (f j)}) j)
          (quotient_torsion R _ (nonzeroPart_ne_zero R (f j)) x)
  | add x y hx hy => exact (Submodule.torsion R _).add_mem hx hy

private theorem from_to_if_freeCoordinates_zero (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (f : Fin n → R)
    (d : ⨁ j : Fin n, R ⧸ Ideal.span {f j})
    (hd : freeCoordinates R n f d = 0) :
    fromTorsionSum R n f (toTorsionSum R n f d) = d := by
  classical
  apply DirectSum.ext_component R
  intro j
  change fromTorsion R (f j) (toTorsion R (f j) (d j)) = d j
  by_cases h : f j = 0
  · have hz : freePart R (f j) (d j) = 0 := by
      have hh := congrArg (fun x : Fin n → R => x j) hd
      simpa [freeCoordinates] using hh
    have hdj : d j = 0 := (freePart_injective R (f j) h) (by simpa using hz)
    rw [hdj, from_to_of_zero R _ h 0]
  · exact from_to_of_ne R _ h (d j)

private theorem freeCoordinates_torsion_zero (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (f : Fin n → R)
    (d : ⨁ j : Fin n, R ⧸ Ideal.span {f j})
    (hd : d ∈ Submodule.torsion R _) : freeCoordinates R n f d = 0 := by
  classical
  funext j
  change freePart R (f j) (d j) = 0
  exact torsion_map_to_ring_zero R
    ((freePart R (f j)).comp (DirectSum.component R (Fin n)
      (fun j => R ⧸ Ideal.span {f j}) j)) hd

private theorem freeCoordinates_zero_iff_torsion (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (f : Fin n → R)
    (d : ⨁ j : Fin n, R ⧸ Ideal.span {f j}) :
    freeCoordinates R n f d = 0 ↔ d ∈ Submodule.torsion R _ := by
  refine ⟨fun hd => ?_, freeCoordinates_torsion_zero R n f d⟩
  rw [← from_to_if_freeCoordinates_zero R n f d hd]
  exact torsion_of_map R (fromTorsionSum R n f) (torsion_torsionSum R n f _)

/-- Let `M` be a finite retract of `D`, let `q : D → F` vanish exactly on the torsion of `D`, where
finite submodules of `F` are free, and let `c ∘ b` fix the torsion of `D`, with `B` torsion. Then
`M ⧸ torsion` is finite free, `M` is its product with its torsion submodule, and that torsion
submodule is a retract of `B`. -/
private theorem split_retract (R : Type*) [CommRing R] [IsDomain R]
    {M D B F : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
    [AddCommGroup F] [Module R F]
    (hF : ∀ (K : Submodule R F), [Module.Finite R K] → Module.Free R K)
    (i : M →ₗ[R] D) (p : D →ₗ[R] M) (hip : p.comp i = LinearMap.id)
    (q : D →ₗ[R] F) (b : D →ₗ[R] B) (c : B →ₗ[R] D)
    (hq : ∀ d, q d = 0 ↔ d ∈ Submodule.torsion R D)
    (hbc : ∀ d, q d = 0 → c (b d) = d)
    (hB : ∀ z : B, z ∈ Submodule.torsion R B) :
    Module.Finite R (M ⧸ Submodule.torsion R M) ∧
    Module.Free R (M ⧸ Submodule.torsion R M) ∧
    Nonempty (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) ∧
    ∃ (it : Submodule.torsion R M →ₗ[R] B)
      (pt : B →ₗ[R] Submodule.torsion R M), pt.comp it = LinearMap.id := by
  classical
  let T := Submodule.torsion R M
  let Q := M ⧸ T
  let l : M →ₗ[R] F := q.comp i
  have hl (x : M) : l x = 0 ↔ x ∈ T := by
    constructor
    · intro hx
      have hi : i x ∈ Submodule.torsion R D := (hq _).mp hx
      have hp := torsion_of_map R p hi
      have hid : p (i x) = x := by simpa using LinearMap.congr_fun hip x
      rwa [hid] at hp
    · exact fun hx => (hq _).mpr (torsion_of_map R i hx)
  let lq : Q →ₗ[R] F := T.liftQ l fun x hx => (hl x).2 hx
  have hlq : Function.Injective lq := by
    refine LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr fun x hx => ?_)
    induction x using Quotient.inductionOn' with
    | h x =>
      apply (Submodule.Quotient.mk_eq_zero T).mpr
      exact (hl x).mp (LinearMap.mem_ker.mp hx)
  let : Module.Finite R Q := Module.Finite.quotient R T
  let : Module.Free R Q := free_of_injective R hF lq hlq
  obtain ⟨s, hs⟩ := T.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr T.mkQ_surjective)
  obtain ⟨e⟩ := nonempty_equiv_prod_of_section R T.mkQ T
    (fun _ => Submodule.Quotient.mk_eq_zero T) s (LinearMap.congr_fun hs)
  let it : T →ₗ[R] B := b.comp (i.comp T.subtype)
  let pt : B →ₗ[R] T := LinearMap.codRestrict T (p.comp c) (by
    intro z
    exact torsion_of_map R p (torsion_of_map R c (hB z)))
  refine ⟨inferInstance, inferInstance, ⟨e⟩, it, pt, ?_⟩
  refine LinearMap.ext fun x => Subtype.ext ?_
  change p (c (b (i x.1))) = x.1
  rw [hbc (i x.1) ((hq _).mpr (torsion_of_map R i x.2))]
  exact LinearMap.congr_fun hip x.1

private theorem isBezout_localization_atPrime (R : Type*) [CommRing R] [IsDomain R] [IsBezout R] :
    ∀ (m : Ideal R) [m.IsMaximal], IsBezout (Localization.AtPrime m) := by
  intro m hm
  let : m.IsPrime := hm.isPrime
  exact (isBezout_localization_and_valuationRing_atPrime_and_iff
    (R := R) (Rₘ := Localization.AtPrime m) (A := Localization.AtPrime m)
    m.primeCompl m).1

private theorem split_torsion_of_finitePresentation
    (R : Type*) [CommRing R] [IsDomain R] [IsBezout R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (hfree : ∀ (n : ℕ) (K : Submodule R (Fin n → R)),
      [Module.Finite R K] → Module.Free R K) :
    Module.Finite R (M ⧸ Submodule.torsion R M) ∧
    Module.Free R (M ⧸ Submodule.torsion R M) ∧
    Nonempty (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) ∧
    ∃ (n : ℕ) (f : Fin n → R),
      (∀ j, f j ≠ 0) ∧
      ∃ (i : Submodule.torsion R M →ₗ[R] ⨁ j, R ⧸ Ideal.span {f j})
        (p : (⨁ j, R ⧸ Ideal.span {f j}) →ₗ[R] Submodule.torsion R M),
        p.comp i = LinearMap.id := by
  classical
  obtain ⟨n, f, i, p, hp⟩ :=
    finitePresentation_summand_fin_directSum_quotient_span_singleton
      R (isBezout_localization_atPrime R) M
  let g : Fin n → R := fun j => nonzeroPart R (f j)
  obtain ⟨hfin, hfr, he, ib, pb, hpb⟩ :=
    split_retract R (hfree n) i p hp
      (freeCoordinates R n f) (toTorsionSum R n f) (fromTorsionSum R n f)
      (freeCoordinates_zero_iff_torsion R n f)
      (from_to_if_freeCoordinates_zero R n f)
      (torsion_torsionSum R n f)
  exact ⟨hfin, hfr, he, n, g, fun j => nonzeroPart_ne_zero R (f j), ib, pb, hpb⟩

/-- Over a Bézout domain, finite submodules of free modules are free. Every finitely presented
module splits as the direct sum of its finite free torsion quotient and its torsion submodule,
which is itself a summand of a finite direct sum of quotients by nonzero principal ideals. -/
@[stacks 0ASU]
theorem finite_submodule_free_and_finitePresentation_split_torsion
    (R : Type u) [CommRing R] [IsDomain R] [IsBezout R] :
    (∀ (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F]
      (N : Submodule R F) [Module.Finite R N], Module.Free R N) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M],
      Module.Finite R (M ⧸ Submodule.torsion R M) ∧
      Module.Free R (M ⧸ Submodule.torsion R M) ∧
      Nonempty (M ≃ₗ[R] (M ⧸ Submodule.torsion R M) × Submodule.torsion R M) ∧
      ∃ (n : ℕ) (f : Fin n → R),
        (∀ j, f j ≠ 0) ∧
        ∃ (i : Submodule.torsion R M →ₗ[R] ⨁ j, R ⧸ Ideal.span {f j})
          (p : (⨁ j, R ⧸ Ideal.span {f j}) →ₗ[R] Submodule.torsion R M),
          p.comp i = LinearMap.id) := by
  exact ⟨fun F _ _ _ N _ => free_finite_submodule R F N, fun M _ _ _ =>
    split_torsion_of_finitePresentation R (M := M) fun n K _ =>
      free_finite_submodule_pi R (Fin n) K⟩
