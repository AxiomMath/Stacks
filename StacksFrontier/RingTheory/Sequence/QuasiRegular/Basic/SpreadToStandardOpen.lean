module

import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeSpan

@[expose] public section

open scoped Finset

@[expose] public section

/-!
# Quasi-regularity spreads out from a prime to a standard open

Let `R` be a Noetherian ring, `M` a finite `R`-module and `f = x₁, …, x_c` a sequence in `R`
generating the ideal `J = (x₁, …, x_c)`. Quasi-regularity of `f` on `M` is bijectivity of the
canonical map of graded `A = (R/J)[X₁, …, X_c]`-modules
`Φ : A ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} JⁿM/J^{n+1}M`, which is always surjective, so it is the
vanishing of `K = ker Φ`.

The source of `Φ` is the base change of `M/JM` along `R/J → A`, hence a finite `A`-module, and `A`
is Noetherian because `R/J` is; therefore `K` is a finite `A`-module. Now the formation of `Φ`
commutes with localization: for a submonoid `T ⊆ R` the canonical map attached to the image
sequence in `T⁻¹R` acting on `T⁻¹M` is the localization of `Φ` at `T`, and localization is exact,
so the image sequence is `T⁻¹M`-quasi-regular exactly when every element of `K` is killed by some
element of `T`.

Applying this at `T = 𝔭ᶜ` turns the hypothesis into: every element of `K` is killed by some
`s ∉ 𝔭`. Picking `A`-module generators `k₁, …, k_t` of `K` and `sᵢ ∉ 𝔭` with `sᵢ kᵢ = 0`, the
single element `g = s₁ ⋯ s_t ∉ 𝔭` kills every `A`-linear combination of the `kᵢ`, hence all of `K`
— the `R`-action commuting with the `A`-action. Applying the same criterion at `T = {1, g, g², …}`
returns quasi-regularity of the image sequence over `R_g` on `M_g`.

## Main results

* `Stacks.QuasiregularSequence.BasicOpenSpread.solution`: Stacks tag 061Q, in the form
  `RingTheory.Sequence.exists_notMem_isQuasiRegular_away_of_isQuasiRegular_atPrime`.

## Implementation notes

The finiteness argument needs only that `K` is generated as an `A`-module by finitely many
elements and that the element `g` of `R` acts on the source commuting with `A`; the homogeneity of
the generators used by the source plays no role, so it is not established here.

That localization commutes with arbitrary direct sums is proved here, in two shapes: for a family,
`Stacks.QuasiregularSequence.BasicOpenSpread.isLocalizedModule_dfinsupp`, and for the constant
family `ι →₀ N`, `Stacks.QuasiregularSequence.BasicOpenSpread.isLocalizedModule_finsupp`. Both are
needed, the target of `Φ` being the direct sum `⨁_{n ≥ 0} JⁿM/J^{n+1}M` outright and its source
`(R/J)[X₁, …, X_c] ⊗_{R/J} (M/JM)` being one after the monomial basis of `(R/J)[X₁, …, X_c]`
identifies it with `(Fin c →₀ ℕ) →₀ (M/JM)`.

That `JⁿM` localizes to `(J')ⁿM'` (`Stacks.QuasiregularSequence.BasicOpenSpread.localized'_JpowM`)
is proved from the description of `JⁿM` as the `R`-span of the elements `f^e m` with `|e| = n`
(`RingTheory.Sequence.JpowM_eq_span`) rather than from flatness of `T⁻¹R`: the denominators of an
element of `M'` are units in `R'`, so they do not enlarge the `R'`-span of the image. Only the
`T`-torsion half of the comparison on targets is needed, so no localization statement is proved for
`⨁ₙ JⁿM/J^{n+1}M` itself.

`RingTheory.Sequence.IsQuasiRegular` is stated for a `List`, whose image sequence is `rs.map
(algebraMap R S)`, while `quasiRegularCanonicalMap` is indexed by `Fin c`; the two are matched by
`Stacks.QuasiregularSequence.BasicOpenSpread.bijective_quasiRegularCanonicalMap_congr`, which
transports bijectivity of the canonical map along an equality of the lengths.

## References

* [StacksProject 061Q](https://stacks.math.columbia.edu/tag/061Q)
-/

namespace Stacks.QuasiregularSequence.BasicOpenSpread

open RingTheory.Sequence

section Reindex

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end Reindex

section GenericLocalization

variable {R : Type*} [CommRing R] (T : Submonoid R)

/-- Precomposing a localization map with a linear equivalence again exhibits the target as a
localization: the three defining conditions only see the isomorphism class of the source. -/
private theorem isLocalizedModule_comp_linearEquiv {P P₀ N : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P₀] [Module R P₀] [AddCommGroup N] [Module R N] (e : P ≃ₗ[R] P₀) (g : P₀ →ₗ[R] N)
    [IsLocalizedModule T g] : IsLocalizedModule T (g ∘ₗ (e : P →ₗ[R] P₀))
    where
  map_units t := IsLocalizedModule.map_units g t
  surj y := by
    obtain ⟨⟨x, t⟩, hx⟩ := IsLocalizedModule.surj T g y
    exact ⟨⟨e.symm x, t⟩, by simpa using hx⟩
  exists_of_eq {x₁ x₂} h := by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) h
    refine ⟨t, e.injective ?_⟩
    simpa only [Submonoid.smul_def, map_smul] using ht

/-- If every component of a finitely supported family is killed by an element of `T`, then one
element of `T` kills the whole family. -/
private theorem exists_mem_smul_eq_zero_dfinsupp {ι : Type*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (x : Π₀ i, N i)
    (h : ∀ i, ∃ t ∈ T, t • x i = 0) : ∃ t ∈ T, t • x = 0 := by
  classical
  choose t ht hx using h
  refine ⟨∏ i ∈ x.support, t i, Submonoid.prod_mem _ fun i _ => ht i, DFinsupp.ext fun i => ?_⟩
  rw [DFinsupp.smul_apply, DFinsupp.zero_apply]
  by_cases hi : i ∈ x.support
  · rw [← Finset.prod_erase_mul _ _ hi, mul_smul, hx i, smul_zero]
  · rw [DFinsupp.notMem_support_iff.1 hi, smul_zero]

/-- **Localization commutes with arbitrary direct sums.**
If each component map `g i : N i → N' i` exhibits `N' i` as the localization of `N i` at `T`, then
`⨁ i, N' i` is the localization of `⨁ i, N i` at `T`, via the map acting componentwise. -/
private theorem isLocalizedModule_dfinsupp {ι : Type*} {N N' : ι → Type*} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, AddCommGroup (N' i)] [∀ i, Module R (N' i)]
    (g : ∀ i, N i →ₗ[R] N' i) [∀ i, IsLocalizedModule T (g i)] :
    IsLocalizedModule T (DFinsupp.mapRange.linearMap g) := by
  classical
  have happ : ∀ (x : Π₀ i, N i) (i : ι), (DFinsupp.mapRange.linearMap g x) i = g i (x i) :=
    fun x i => DFinsupp.mapRange_apply (fun i => (g i : N i → N' i)) (fun i => map_zero (g i)) x i
  have hof :
    ∀ (i : ι) (x : N i),
      DFinsupp.mapRange.linearMap g (DirectSum.of N i x) = DirectSum.of N' i (g i x) :=
    fun _ _ => DFinsupp.mapRange_single (hf := fun i => map_zero (g i))
  refine ⟨?_, ?_, ?_⟩
  · intro t
    obtain ⟨u, hu⟩ :
      ∃ u : ∀ i, (Module.End R (N' i))ˣ,
        ∀ i, (u i : Module.End R (N' i)) = algebraMap R (Module.End R (N' i)) (t : R) :=
      ⟨fun i => (IsLocalizedModule.map_units (g i) t).unit, fun _ => IsUnit.unit_spec _⟩
    refine
      ⟨⟨algebraMap R (Module.End R (Π₀ i, N' i)) (t : R),
          DFinsupp.mapRange.linearMap (fun i => ((u i)⁻¹).val), ?_, ?_⟩,
        rfl⟩
    · refine LinearMap.ext fun x => DFinsupp.ext fun i => ?_
      have h1 : (algebraMap R (Module.End R (N' i)) (t : R)) (((u i)⁻¹).val (x i)) = x i := by
        rw [← hu i, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
      simpa [Module.algebraMap_end_apply, DFinsupp.mapRange_apply] using h1
    · refine LinearMap.ext fun x => DFinsupp.ext fun i => ?_
      have h1 : ((u i)⁻¹).val ((algebraMap R (Module.End R (N' i)) (t : R)) (x i)) = x i := by
        rw [← hu i, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
      simpa [Module.algebraMap_end_apply, DFinsupp.mapRange_apply] using h1
  · intro y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | of i yi =>
      obtain ⟨⟨xi, t⟩, hxi⟩ := IsLocalizedModule.surj T (g i) yi
      refine ⟨⟨DirectSum.of N i xi, t⟩, ?_⟩
      have key : (t : R) • (DirectSum.of N' i yi) = DirectSum.of N' i ((t : R) • yi) :=
        ((DirectSum.lof R ι N' i).map_smul (t : R) yi).symm
      simp only [Submonoid.smul_def] at hxi ⊢
      rw [hof, ← hxi, key]
    | add a b ha hb =>
      obtain ⟨⟨xa, ta⟩, hxa⟩ := ha
      obtain ⟨⟨xb, tb⟩, hxb⟩ := hb
      refine ⟨⟨(tb : R) • xa + (ta : R) • xb, ta * tb⟩, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, map_add, map_smul] at hxa hxb ⊢
      rw [← hxa, ← hxb, smul_add, smul_smul, smul_smul, mul_comm (tb : R) (ta : R)]
  · intro x₁ x₂ h
    have hx : DFinsupp.mapRange.linearMap g (x₁ - x₂) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨t, ht, hzero⟩ := exists_mem_smul_eq_zero_dfinsupp T (x₁ - x₂) fun i => by
      have hgi : g i ((x₁ - x₂) i) = g i 0 := by
        rw [map_zero, ← happ, hx]; rfl
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g i) hgi
      exact ⟨c, c.2, by simpa only [Submonoid.smul_def, smul_zero] using hc⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    have hfin := sub_eq_zero.1 (by simpa only [smul_sub] using hzero)
    simpa only [Submonoid.smul_def] using hfin

/-- **Localization commutes with arbitrary direct sums of copies of one module.** The `Finsupp`
presentation of `Stacks.QuasiregularSequence.BasicOpenSpread.isLocalizedModule_dfinsupp` for a
constant family, which is the shape in which the source of the canonical map is a direct sum. -/
private theorem isLocalizedModule_finsupp {ι : Type*} {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule T g] :
    IsLocalizedModule T (Finsupp.mapRange.linearMap g : (ι →₀ N) →ₗ[R] ι →₀ N') := by
  classical
  let e : (ι →₀ N) ≃ₗ[R] Π₀ _ : ι, N := finsuppLequivDFinsupp R
  let e' : (ι →₀ N') ≃ₗ[R] Π₀ _ : ι, N' := finsuppLequivDFinsupp R
  have := isLocalizedModule_dfinsupp T fun _ : ι => g
  have := isLocalizedModule_comp_linearEquiv T e (DFinsupp.mapRange.linearMap fun _ : ι => g)
  have := IsLocalizedModule.of_linearEquiv T
    ((DFinsupp.mapRange.linearMap fun _ : ι => g) ∘ₗ (e : (ι →₀ N) →ₗ[R] _)) e'.symm
  convert this using 1
  exact LinearMap.ext fun x => Finsupp.ext fun i => by simp [e, e']

end GenericLocalization

section Monomials

variable {R : Type*} [CommRing R]

end Monomials

section Comparison

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (T : Submonoid R)
  {c : ℕ} (f : Fin c → R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization T R']
  (M' : Type*) [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
  (l : M →ₗ[R] M') [IsLocalizedModule T l]

/-- **An element lands in a localized submodule exactly when some denominator pushes it in.**
For a submodule `K ⊆ N` and a localization `g : N → N'` at `T`, the image `g m` lies in the
localized submodule `T⁻¹K` if and only if `t m ∈ K` for some `t ∈ T`. -/
private theorem mem_localized'_iff {N : Type*} [AddCommGroup N] [Module R N] (S : Type*)
    [CommRing S] [Algebra R S] {N' : Type*} [AddCommGroup N'] [Module R N'] [Module S N']
    [IsScalarTower R S N'] [IsLocalization T S] (g : N →ₗ[R] N') [IsLocalizedModule T g]
    (K : Submodule R N) (m : N) : g m ∈ K.localized' S T g ↔ ∃ t : T, (t : R) • m ∈ K := by
  rw [Submodule.mem_localized']
  constructor
  · rintro ⟨k, hk, s, hs⟩
    have h1 : g k = g ((s : R) • m) := by
      rw [map_smul, ← hs]
      exact (IsLocalizedModule.mk'_cancel' g k s).symm
    obtain ⟨cc, hcc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := g) h1
    simp only [Submonoid.smul_def] at hcc
    refine ⟨cc * s, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← hcc]
    exact K.smul_mem _ hk
  · rintro ⟨t, ht⟩
    refine ⟨(t : R) • m, ht, t, ?_⟩
    rw [← Submonoid.smul_def]
    exact IsLocalizedModule.mk'_cancel g m t

/-- **`JⁿM` localizes to `(J')ⁿM'`.**
Both sides are the span of the elements `f^e y` with `|e| = n`, over `R` and `R'` respectively;
the denominators of `y ∈ M'` are units in `R'`, so they do not enlarge the span. -/
private theorem localized'_JpowM (n : ℕ) :
    (JpowM M f n).localized' R' T l = JpowM M' (fun i => algebraMap R R' (f i)) n := by
  rw [JpowM_eq_span, Submodule.localized'_span, JpowM_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, ⟨e, m, he, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨e, l m, he, ?_⟩
    rw [map_smul, ← fpow_algebraMap, algebraMap_smul]
  · rw [Submodule.span_le]
    rintro y ⟨e, y', he, rfl⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective T l y'
    obtain ⟨u, hu⟩ := IsLocalization.map_units R' s
    have hs : (u : R') • IsLocalizedModule.mk' l m s = l m := by
      rw [hu, algebraMap_smul, ← Submonoid.smul_def]
      exact IsLocalizedModule.mk'_cancel' l m s
    have key :
      fpow (fun i => algebraMap R R' (f i)) e • l m ∈
        Submodule.span R'
          (l '' {x : M | ∃ (e : Fin c →₀ ℕ) (m : M), qrMdeg e = n ∧ x = fpow f e • m}) := by
      refine Submodule.subset_span ⟨fpow f e • m, ⟨e, m, he, rfl⟩, ?_⟩
      rw [map_smul, ← fpow_algebraMap, algebraMap_smul]
    rw [← hs, smul_comm] at key
    have h3 := Submodule.smul_mem _ ((u⁻¹ : R'ˣ) : R') key
    rwa [smul_smul, Units.inv_mul, one_smul] at h3

/-- The elementwise form of `Stacks.QuasiregularSequence.BasicOpenSpread.localized'_JpowM`. -/
private theorem mem_JpowM_map_iff (n : ℕ) (m : M) :
    l m ∈ JpowM M' (fun i => algebraMap R R' (f i)) n ↔ ∃ t : T, (t : R) • m ∈ JpowM M f n := by
  rw [← localized'_JpowM T f R' M' l n, mem_localized'_iff T R' l]

/-- The `n = 1` case of `Stacks.QuasiregularSequence.BasicOpenSpread.localized'_JpowM`, in the
shape in which `M/JM` occurs. -/
private theorem localized'_Jid_smul_top :
    (Jid f • (⊤ : Submodule R M)).localized' R' T l =
      Jid (fun i => algebraMap R R' (f i)) • (⊤ : Submodule R' M') := by
  have h1 : (Jid f • (⊤ : Submodule R M)) = JpowM M f 1 := by rw [JpowM, pow_one]
  have h2 :
    (Jid (fun i => algebraMap R R' (f i)) • (⊤ : Submodule R' M')) =
      JpowM M' (fun i => algebraMap R R' (f i)) 1 := by
    rw [JpowM, pow_one]
  rw [h1, h2, localized'_JpowM]

private theorem isLocalizedModule_barMap : IsLocalizedModule T (barMap R' f l) := by
  have heq : barMap R' f l =
      ((Submodule.quotEquivOfEq _ _ (localized'_Jid_smul_top T f R' M' l)).restrictScalars R :
            _ ≃ₗ[R] _).toLinearMap ∘ₗ
        (Jid f • (⊤ : Submodule R M)).toLocalizedQuotient' R' T l := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H m => rfl
  rw [heq]
  exact IsLocalizedModule.of_linearEquiv T _ _

private theorem isLocalizedModule_srcMap : IsLocalizedModule T (srcMap R' f l) := by
  have := isLocalizedModule_barMap T f R' M' l
  have :
    IsLocalizedModule T
      (Finsupp.mapRange.linearMap (barMap R' f l) : ((Fin c →₀ ℕ) →₀ qrMbar M f) →ₗ[R] _) :=
    isLocalizedModule_finsupp T _
  have :=
    isLocalizedModule_comp_linearEquiv T ((srcFinsuppEquiv M f).restrictScalars R)
      (Finsupp.mapRange.linearMap (barMap R' f l))
  exact IsLocalizedModule.of_linearEquiv T _ _

/-- **The target of the canonical map is `T`-torsion-free modulo its localization.**
An element of `JⁿM/J^{n+1}M` killed by the comparison map is killed by an element of `T`: its
representative is carried into `(J')^{n+1}M'`, so some denominator carries it into `J^{n+1}M`. -/
private theorem exists_smul_eq_zero_of_tgtMapComp (n : ℕ) (y : Tcomp M f n)
    (h : tgtMapComp R' f l n y = 0) : ∃ t : T, (t : R) • y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [tgtMapComp_mk] at h
    have h1 : l (x : M) ∈ JpowM M' (fun i => algebraMap R R' (f i)) (n + 1) := by
      simpa only [Tsub, Submodule.mem_comap, Submodule.coe_subtype] using
        (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨t, ht⟩ := (mem_JpowM_map_iff T f R' M' l (n + 1) (x : M)).1 h1
    refine ⟨t, ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    simpa only [Tsub, Submodule.mem_comap, Submodule.coe_subtype, SetLike.val_smul] using ht

/-- An element of `⨁ₙ JⁿM/J^{n+1}M` killed by the comparison map is killed by an element of `T`:
finitely many components, one denominator each. -/
private theorem exists_smul_eq_zero_of_tgtMap (x : Target M f) (h : tgtMap R' f l x = 0) :
    ∃ t ∈ T, t • x = 0 := by
  classical
  refine exists_mem_smul_eq_zero_dfinsupp T x fun n => ?_
  obtain ⟨t, ht⟩ := exists_smul_eq_zero_of_tgtMapComp T f R' M' l n (x n) (by
    have hn : (tgtMap R' f l x) n = tgtMapComp R' f l n (x n) :=
      DFinsupp.mapRange_apply (fun n => (tgtMapComp R' f l n : Tcomp M f n → _))
        (fun n => map_zero (tgtMapComp R' f l n)) x n
    rw [← hn, h]
    rfl)
  exact ⟨t, t.2, ht⟩

end Comparison

/-- **Localization detects quasi-regularity through the kernel of the canonical map.**
For a submonoid `T` of `R`, a localization `R'` of `R` at `T` and a localization `M'` of `M` at
`T`, the image sequence `T⁻¹f` is `M'`-quasi-regular if and only if every element of the kernel of
the canonical map of `f` on `M` is annihilated by some element of `T`.

The canonical map of the localized data is the localization of the canonical map of `f`
(`Stacks.QuasiregularSequence.BasicOpenSpread.quasiRegularCanonicalMap_srcMap`), and localization
is exact, so its kernel is the localization of `LinearMap.ker (quasiRegularCanonicalMap f)`; that
localization vanishes exactly when each of its elements is `T`-torsion. Surjectivity of the
localized map is automatic. -/
private theorem bijective_quasiRegularCanonicalMap_localization_iff {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (T : Submonoid R) {c : ℕ} (f : Fin c → R)
    (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization T R'] (M' : Type*) [AddCommGroup M']
    [Module R M'] [Module R' M'] [IsScalarTower R R' M'] (l : M →ₗ[R] M') [IsLocalizedModule T l] :
    Function.Bijective (quasiRegularCanonicalMap (M := M') fun i => algebraMap R R' (f i)) ↔
      ∀ k ∈ LinearMap.ker (quasiRegularCanonicalMap (M := M) f), ∃ t ∈ T, t • k = 0 := by
  have := isLocalizedModule_srcMap T f R' M' l
  have hsq := quasiRegularCanonicalMap_srcMap R' f l
  constructor
  · intro hbij k hk
    have h0 : srcMap R' f l k = 0 := by
      refine hbij.1 ?_
      rw [hsq, LinearMap.mem_ker.1 hk, map_zero, map_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (srcMap R' f l)).1 h0
    exact ⟨t, t.2, ht⟩
  · intro hK
    refine ⟨IsLocalizedModule.injective_of_map_zero (S := T) (srcMap R' f l) (g :=
      (quasiRegularCanonicalMap (M := M') (fun i => algebraMap R R' (f i))).restrictScalars R)
        fun k hk => ?_, quasiRegularCanonicalMap_surjective _⟩
    rw [LinearMap.coe_restrictScalars, hsq] at hk
    obtain ⟨t', ht'mem, ht'⟩ := exists_smul_eq_zero_of_tgtMap T f R' M' l _ hk
    obtain ⟨t'', ht''mem, ht''eq⟩ :=
      hK (t' • k) (by rwa [LinearMap.mem_ker, LinearMap.map_smul_of_tower])
    exact
      (IsLocalizedModule.eq_zero_iff T (srcMap R' f l)).2
        ⟨⟨t'' * t', mul_mem ht''mem ht'mem⟩,
          show (t'' * t') • k = 0 by rwa [mul_smul]⟩

/-- If every element of the kernel of the canonical map is annihilated by some element of the
submonoid `T`, then a single element of `T` annihilates the whole kernel: the kernel is a finite
module over `(R/J)[X₁, …, X_c]`, so the product of annihilators of a finite generating family
works. -/
private theorem exists_mem_forall_smul_ker_eq_zero {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {c : ℕ} (f : Fin c → R)
    (T : Submonoid R)
    (h : ∀ k ∈ LinearMap.ker (quasiRegularCanonicalMap (M := M) f), ∃ t ∈ T, t • k = 0) :
    ∃ t ∈ T, ∀ k ∈ LinearMap.ker (quasiRegularCanonicalMap (M := M) f), t • k = 0 := by
  classical
  have hfinbar : Module.Finite (qrRbar f) (qrMbar M f) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hfin : Module.Finite (MvPolynomial (Fin c) (qrRbar f)) (Source M f) :=
    Module.Finite.base_change _ _ _
  have hnoeth : IsNoetherian (MvPolynomial (Fin c) (qrRbar f)) (Source M f) := inferInstance
  set Φ : Source M f →ₗ[MvPolynomial (Fin c) (qrRbar f)] Target M f :=
    { toFun := quasiRegularCanonicalMap f
      map_add' := (quasiRegularCanonicalMap f).map_add
      map_smul' := fun a s => canonicalMap_MvPolynomial_linear f a s } with hΦ
  have hmem :
    ∀ k : Source M f,
      k ∈ LinearMap.ker Φ ↔ k ∈ LinearMap.ker (quasiRegularCanonicalMap (M := M) f) :=
    fun k => by simp [LinearMap.mem_ker, hΦ]
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (LinearMap.ker Φ)
  have hsker : ∀ k ∈ s, k ∈ LinearMap.ker (quasiRegularCanonicalMap (M := M) f) := fun k hk =>
    (hmem k).1 (by
      rw [← hs]
      exact Submodule.subset_span hk)
  choose! t ht hts using h
  refine ⟨∏ k ∈ s, t k, Submonoid.prod_mem _ fun k hk => ht k (hsker k hk), ?_⟩
  have main :
    ∀ k ∈ Submodule.span (MvPolynomial (Fin c) (qrRbar f)) (s : Set (Source M f)),
      (∏ k ∈ s, t k) • k = 0 := by
    intro k hk
    induction hk using Submodule.span_induction with
    | mem x hx => rw [← Finset.prod_erase_mul s t hx, mul_smul, hts x (hsker x hx), smul_zero]
    | zero => exact smul_zero _
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_comm, hx, smul_zero]
  intro k hk
  exact
    main k
      (by
        rw [hs]; exact (hmem k).2 hk)

/-- **Stacks 061Q.** Let `R` be a Noetherian ring, `M` a finite `R`-module, `𝔭 ⊂ R` a prime and
`rs` a sequence of elements of `R` whose image in `R_𝔭` is `M_𝔭`-quasi-regular. Then there is a
`g ∈ R`, `g ∉ 𝔭`, such that the image of `rs` in `R_g` is `M_g`-quasi-regular. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime] (rs : List R) (Rₚ : Type*)
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] (Mₚ : Type*) [AddCommGroup Mₚ]
    [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (fₚ : M →ₗ[R] Mₚ)
    [IsLocalizedModule p.primeCompl fₚ] (hp : IsQuasiRegular Mₚ (rs.map (algebraMap R Rₚ))) :
    ∃ g ∉ p,
      ∀ (Rg : Type*) [CommRing Rg] [Algebra R Rg] [IsLocalization.Away g Rg] (Mg : Type*)
        [AddCommGroup Mg] [Module R Mg] [Module Rg Mg] [IsScalarTower R Rg Mg] (fg : M →ₗ[R] Mg)
        [IsLocalizedModule (Submonoid.powers g) fg],
        IsQuasiRegular Mg (rs.map (algebraMap R Rg)) := by
  obtain ⟨g, hg, hgk⟩ :=
    exists_mem_forall_smul_ker_eq_zero (M := M) (fun i : Fin rs.length => rs[i]) p.primeCompl
      ((bijective_quasiRegularCanonicalMap_localization_iff p.primeCompl _ Rₚ Mₚ fₚ).1
        ((isQuasiRegular_map_iff rs Rₚ Mₚ).1 hp))
  refine ⟨g, hg, ?_⟩
  intro Rg _ _ _ Mg _ _ _ _ fg _
  refine
    (isQuasiRegular_map_iff rs Rg Mg).2
      ((bijective_quasiRegularCanonicalMap_localization_iff (Submonoid.powers g) _ Rg Mg fg).2
        fun k hk => ⟨g, Submonoid.mem_powers g, hgk k hk⟩)

end Stacks.QuasiregularSequence.BasicOpenSpread

/-!
# Quasi-regularity spreads out from a prime to a standard open

Let `R` be a Noetherian ring, `M` a finite `R`-module and `x₁, …, x_c` a sequence of elements of
`R`. Quasi-regularity of this sequence is a condition on the canonical map
`Φ : (R/J)[X₁, …, X_c] ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} JⁿM/J^{n+1}M`, `J = (x₁, …, x_c)`, and hence a
condition on the kernel `K` of `Φ`, which is a graded module over `(R/J)[X₁, …, X_c]`. If the
sequence becomes `M_𝔭`-quasi-regular after localizing at a prime `𝔭`, then `K` dies in that
localization; since `(R/J)[X₁, …, X_c]` is Noetherian and the source of `Φ` is a finite module
over it, `K` is generated by finitely many homogeneous elements `k₁, …, k_t`, each killed by some
`gᵢ ∉ 𝔭`, and the single element `g = g₁ ⋯ g_t ∉ 𝔭` kills all of `K`. So quasi-regularity already
holds over `R_g` for `M_g`: a condition verified at one prime is verified on a whole standard
open neighbourhood of it.

## Main results

* `RingTheory.Sequence.exists_notMem_isQuasiRegular_away_of_isQuasiRegular_atPrime`: if the image
  of a sequence in `R_𝔭` is `M_𝔭`-quasi-regular, then there is a `g ∉ 𝔭` whose image in `R_g` is
  `M_g`-quasi-regular.

## Implementation notes

Both localizations are abstract: the hypothesis speaks of any `Rₚ` with `IsLocalization.AtPrime
Rₚ 𝔭` together with any `Mₚ` localized from `M` at `𝔭.primeCompl`, and the conclusion asserts
quasi-regularity over *every* model `R_g`, `M_g` of the localization away from `g`, so that no
user has to transport the conclusion along an isomorphism with a chosen construction. The two
`IsScalarTower` hypotheses say that the localized module is a module over the localized ring
compatibly with `R`, which is what makes `M_g` an `R_g`-module and the statement one about
`R_g`-modules.

Every hypothesis is used by the conclusion: `IsNoetherianRing R` and `Module.Finite R M` are what
make the kernel of the canonical map a finite module over `(R/J)[X₁, …, X_c]`, hence generated by
finitely many homogeneous elements — without them a single `g` need not kill the whole kernel —
and `hp` is the source's hypothesis at `𝔭`. The scalars are the source's on both sides: the
hypothesis is quasi-regularity of the image sequence `rs.map (algebraMap R Rₚ) : List Rₚ` on the
`Rₚ`-module `Mₚ`, and the conclusion the same over `R_g` on `M_g`; neither is a statement about
`R`-linear data. The canonical map of the source is pinned rather than merely asserted to exist,
since `IsQuasiRegular` is bijectivity of the named map `quasiRegularCanonicalMap`, and the
localizations are pinned by `IsLocalization.AtPrime`, `IsLocalization.Away` and
`IsLocalizedModule` rather than by an unspecified isomorphism. The instantiation is not
degenerate: for `R = k[x₁, …, x_c]`, `M = R`, `rs = [x₁, …, x_c]` and `𝔭 = (x₁, …, x_c)` the
hypothesis holds and `g = 1` is a witness for the conclusion.

The sequence is a `List R`, as in `RingTheory.Sequence.IsQuasiRegular`, and the source's "image of
`x₁, …, x_c` in `R_𝔭`" is `rs.map (algebraMap R Rₚ)`, the image sequence in the same order.

## References

* [StacksProject 061Q](https://stacks.math.columbia.edu/tag/061Q)

## Tags

quasi-regular sequence, localization, Noetherian ring
-/

namespace RingTheory.Sequence

/-- **Stacks 061Q.** Let `R` be a Noetherian ring, `M` a finite `R`-module, `𝔭 ⊂ R` a prime and
`rs = x₁, …, x_c` a sequence of elements of `R` whose image in `R_𝔭` is `M_𝔭`-quasi-regular. Then
there is a `g ∈ R`, `g ∉ 𝔭`, such that the image of `rs` in `R_g` is `M_g`-quasi-regular. -/
@[stacks 061Q]
public theorem exists_notMem_isQuasiRegular_away_of_isQuasiRegular_atPrime {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (rs : List R) (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ]
    [IsScalarTower R Rₚ Mₚ] (fₚ : M →ₗ[R] Mₚ) [IsLocalizedModule p.primeCompl fₚ]
    (hp : IsQuasiRegular Mₚ (rs.map (algebraMap R Rₚ))) :
    ∃ g ∉ p,
      ∀ (Rg : Type*) [CommRing Rg] [Algebra R Rg] [IsLocalization.Away g Rg] (Mg : Type*)
        [AddCommGroup Mg] [Module R Mg] [Module Rg Mg] [IsScalarTower R Rg Mg] (fg : M →ₗ[R] Mg)
        [IsLocalizedModule (Submonoid.powers g) fg],
        IsQuasiRegular Mg (rs.map (algebraMap R Rg)) :=
  Stacks.QuasiregularSequence.BasicOpenSpread.solution p rs Rₚ Mₚ fₚ hp

end RingTheory.Sequence

end
