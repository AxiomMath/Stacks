module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkModuleLevels
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecialization
public import StacksFrontier.RingTheory.AdicCompletion.ModuleEquivOfQuotientEquiv
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.Localization.SubmonoidChange

/-!
# The adic completion of a localized module, over the comparison of the two localizations

`Stacks.Algebraization.adicCompletionLocalizationAlgEquiv` identifies the `J`-adic completion of
`R_𝔭` with the `J`-adic completion of `(R^∧)_𝔮`. This file does the same for a module: for an
`R`-module `M`, the `J`-adic completion of `M_𝔭` is the `J`-adic completion of `(M^∧)_𝔮`, and the
identification lies over the ring one.

That is the comparison a statement about a completed stalk needs in order to be read at a prime
of a chart. The level-`n` reason is the one at the ring level: both sides are localizations of
`M ⧸ JⁿM` at corresponding multiplicative sets. The substance is that the correspondence of the
multiplicative sets is visible on a module annihilated by `JⁿR^∧`, because an element of `R^∧`
outside `𝔮` agrees modulo `JⁿR^∧` with the image of an element of `R` outside `𝔭`, so the two
act identically.

## Main definitions

* `Stacks.Algebraization.levelModuleEquiv` — the level-`n` comparison of the two localized
  modules.
* `Stacks.Algebraization.adicCompletionLocalizationAddEquiv` — **the comparison itself**: the
  `J`-adic completion of `M_𝔭` as the `J`-adic completion of `(M^∧)_𝔮`.

## Main results

* `Stacks.Algebraization.exists_notMem_algebraMap_sub_mem_map_pow` — an element of `R^∧` outside
  `𝔮` agrees modulo `JⁿR^∧` with the image of an element of `R` outside `𝔭`.
* `Stacks.Algebraization.isLocalizedModule_algebraMapSubmonoid_levelLocalizationMap` and
  `Stacks.Algebraization.isLocalizedModule_levelLocalizationMapCompletion` — the level-`n`
  quotient of `(M^∧)_𝔮` is a localization of the level-`n` quotient of `M` at the complement of
  `𝔭`, first over `R^∧` and then over `R`. This is the substance.
* `Stacks.Algebraization.levelModuleEquiv_mk`,
  `Stacks.Algebraization.transitionMap_levelModuleEquiv` — the clauses of the level comparison:
  what it does on the classes coming from `M`, and its compatibility with the transition maps.
* `Stacks.Algebraization.val_adicCompletionLocalizationAddEquiv`,
  `Stacks.Algebraization.adicCompletionLocalizationAddEquiv_of`,
  `Stacks.Algebraization.adicCompletionLocalizationAddEquiv_algebraMap_smul` and
  `Stacks.Algebraization.eq_adicCompletionLocalizationAddEquiv_of_val` — the clauses that
  characterize the comparison: its level-`n` component, its value on the canonical image of an
  element of `M`, its compatibility with the scalars from `R` (which is how it lies over the ring
  comparison, that one being an equivalence of `R`-algebras), and the uniqueness the first of
  those supplies.

## Implementation notes

The two localizations are presented abstractly, by `IsLocalization` and `IsLocalizedModule`
hypotheses, as at the ring level.

The comparison is delivered as an additive equivalence together with its clauses rather than as
a bundled semilinear equivalence. The reason is an instance one: the two sides are modules over
`Rp` and over `Rq`, and there is no `Module R (AdicCompletion (J·Rp) Mp)` instance to make an
`R`-linear statement, while a bundled `≃ₛₗ` would require supplying `RingHomInvPair` instances
for the ring comparison. The level-`n` comparisons it is assembled from ARE `R`-linear
(`levelModuleEquiv`), so no linearity is lost: it is recorded one level at a time, and
`AdicCompletion.addEquivOfQuotientEquiv_smul` turns a ring equivalence matching the levels into
semilinearity of the whole.

No declaration here carries a `stacks` attribute: this is the substrate on which the local
statements of the chapter on algebraic and formal geometry are phrased, not the content of a tag.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Algebraization

/-- A scalar that carries every element of a module into a submodule acts as zero on the
quotient by that submodule. -/
theorem smul_eq_zero_of_forall_smul_mem {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Algebra A B] {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (P : Submodule B N) {r : A} (hr : ∀ y : N, r • y ∈ P) (x : N ⧸ P) :
    r • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hr y

section Compare

variable {R : Type u} [CommRing R] (J : Ideal R) {p : Ideal R}

/-- **An element of the completion outside `𝔮` agrees, modulo `JⁿR^∧`, with the image of an
element of `R` outside `𝔭`.**

This is `Stacks.Algebraization.exists_notMem_evalₐ_eq_mk` read as a congruence rather than as an
equality of level-`n` images: the kernel of the level-`n` evaluation is `JⁿR^∧`. -/
theorem exists_notMem_algebraMap_sub_mem_map_pow (hJ : J.FG) [p.IsPrime] (hJp : J ≤ p) (n : ℕ)
    {t : AdicCompletion J R} (ht : t ∉ (adicPrimeOver J hJp).asIdeal) :
    ∃ a : R, a ∉ p ∧ t - algebraMap R (AdicCompletion J R) a ∈
      (J ^ n).map (algebraMap R (AdicCompletion J R)) := by
  obtain ⟨a, ha, hat⟩ := exists_notMem_evalₐ_eq_mk J hJ hJp n ht
  refine ⟨a, ha, ?_⟩
  rw [← AdicCompletion.ker_evalₐ_eq_map_pow J hJ n, RingHom.mem_ker]
  change (AdicCompletion.evalₐ J n).toRingHom (t - algebraMap R (AdicCompletion J R) a) = 0
  rw [map_sub, sub_eq_zero]
  change AdicCompletion.evalₐ J n t = AdicCompletion.evalₐ J n _
  rw [hat]
  exact (AdicCompletion.evalₐ_of J n a).symm

end Compare

section ModuleLevel

variable {R : Type u} [CommRing R] (J : Ideal R) {p : Ideal R}
  (hJ : J.FG) [p.IsPrime] (hJp : J ≤ p)
  {M : Type v} [AddCommGroup M] [Module R M]
  (Rq : Type w) [CommRing Rq] [Algebra (AdicCompletion J R) Rq] [Algebra R Rq]
    [IsScalarTower R (AdicCompletion J R) Rq]
    [IsLocalization (adicPrimeOver J hJp).asIdeal.primeCompl Rq]
  {Mq : Type w} [AddCommGroup Mq] [Module (AdicCompletion J R) Mq] [Module Rq Mq]
    [Module R Mq] [IsScalarTower (AdicCompletion J R) Rq Mq] [IsScalarTower R Rq Mq]
    [IsScalarTower R (AdicCompletion J R) Mq]
  (fq : AdicCompletion J M →ₗ[AdicCompletion J R] Mq)
    [IsLocalizedModule (adicPrimeOver J hJp).asIdeal.primeCompl fq]

/-- An element of `Iⁿ` acts as zero on the quotient of a module by `Iⁿ` times the module. -/
private theorem smul_eq_zero_of_mem_pow_quotient {A N : Type*} [CommRing A] [AddCommGroup N]
    [Module A N] {I : Ideal A} {n : ℕ} {t : A} (ht : t ∈ I ^ n)
    (x : N ⧸ (I ^ n • (⊤ : Submodule A N))) : t • x = 0 :=
  smul_eq_zero_of_forall_smul_mem _ (fun _ => Submodule.smul_mem_smul ht Submodule.mem_top) x

/-- The image of the complement of `𝔭` lies in the complement of `𝔮`, because `𝔮` contracts to
`𝔭`. -/
theorem algebraMapSubmonoid_le_primeCompl_adicPrimeOver :
    Algebra.algebraMapSubmonoid (AdicCompletion J R) p.primeCompl ≤
      (adicPrimeOver J hJp).asIdeal.primeCompl := by
  rintro _ ⟨a, ha, rfl⟩
  intro hmem
  exact ha (by rw [← comap_adicPrimeOver J hJp]; exact hmem)

omit [Algebra R Rq] [IsScalarTower R (AdicCompletion J R) Rq] [Module R Mq]
  [IsScalarTower R Rq Mq] [IsScalarTower R (AdicCompletion J R) Mq] in
include hJ in
/-- **The level-`n` quotient of `(M^∧)_𝔮` is a localization at the image of the complement of
`𝔭`.**

It is one at the complement of `𝔮` by construction. The two submonoids give the same
localization here because the module is annihilated by `JⁿR^∧`: an element of `R^∧` outside `𝔮`
differs from the image of an element of `R` outside `𝔭` by an element of `JⁿR^∧`, which acts as
zero on both sides. -/
theorem isLocalizedModule_algebraMapSubmonoid_levelLocalizationMap (n : ℕ) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (AdicCompletion J R) p.primeCompl)
      (levelLocalizationMap (J.map (algebraMap R (AdicCompletion J R)))
        (adicPrimeOver J hJp).asIdeal.primeCompl Rq fq n) := by
  refine IsLocalizedModule.of_le_of_smul_eq
    (adicPrimeOver J hJp).asIdeal.primeCompl
    (Algebra.algebraMapSubmonoid (AdicCompletion J R) p.primeCompl) _
    (algebraMapSubmonoid_le_primeCompl_adicPrimeOver J hJp) ?_
  intro t ht
  obtain ⟨a, ha, hsub⟩ := exists_notMem_algebraMap_sub_mem_map_pow J hJ hJp n ht
  have hmem : t - algebraMap R (AdicCompletion J R) a ∈
      (J.map (algebraMap R (AdicCompletion J R))) ^ n := by
    rwa [← Ideal.map_pow]
  refine ⟨algebraMap R (AdicCompletion J R) a, ⟨a, ha, rfl⟩, ?_, ?_⟩
  · intro x
    have h0 := smul_eq_zero_of_mem_pow_quotient hmem x
    rwa [sub_smul, sub_eq_zero] at h0
  · intro y
    have hmap : algebraMap (AdicCompletion J R) Rq (t - algebraMap R (AdicCompletion J R) a) ∈
        ((J.map (algebraMap R (AdicCompletion J R))).map
          (algebraMap (AdicCompletion J R) Rq)) ^ n := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hmem
    have h0 := smul_eq_zero_of_mem_pow_quotient hmap y
    rwa [algebraMap_smul Rq, sub_smul, sub_eq_zero] at h0

/-- The level-`n` quotient of `M` identified with the level-`n` quotient of `M^∧`, read for the
powers of the extended ideal. Both steps are the identity on residue classes. -/
def levelCompletionEquiv (n : ℕ) :
    (M ⧸ (J ^ n • (⊤ : Submodule R M))) ≃ₗ[R]
      (AdicCompletion J M ⧸ ((J.map (algebraMap R (AdicCompletion J R))) ^ n •
        (⊤ : Submodule (AdicCompletion J R) (AdicCompletion J M)))) :=
  (AdicCompletion.quotPowSMulTopEquiv hJ M n).symm.trans
    (quotEquivMapPowModule J (AdicCompletion J R) (AdicCompletion J M) rfl n)

/-- Extending `J` to `R^∧` and then to `Rq` is extending it to `Rq` directly. -/
theorem map_map_eq_map_algebraMap :
    (J.map (algebraMap R (AdicCompletion J R))).map (algebraMap (AdicCompletion J R) Rq) =
      J.map (algebraMap R Rq) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The level-`n` stage of the tower of `Mq` for the ideal extended through `R^∧`, identified
with the stage for the ideal extended from `R` directly. -/
def levelQuotEquivTower (n : ℕ) :
    (Mq ⧸ (((J.map (algebraMap R (AdicCompletion J R))).map
        (algebraMap (AdicCompletion J R) Rq)) ^ n • (⊤ : Submodule Rq Mq))) ≃ₗ[Rq]
      (Mq ⧸ ((J.map (algebraMap R Rq)) ^ n • (⊤ : Submodule Rq Mq))) :=
  Submodule.quotEquivOfEq _ _ (by rw [map_map_eq_map_algebraMap J Rq])

/-- **What `levelCompletionEquiv` does**: it carries the class of `m : M` to the class of the
canonical image of `m` in the completion. -/
@[simp]
theorem levelCompletionEquiv_mk (n : ℕ) (m : M) :
    levelCompletionEquiv J hJ n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (AdicCompletion.of J M m) := by
  have h : AdicCompletion.quotPowSMulTopEquiv hJ M n
      (Submodule.Quotient.mk (AdicCompletion.of J M m)) = Submodule.Quotient.mk m := rfl
  rw [levelCompletionEquiv, LinearEquiv.trans_apply, ← h, LinearEquiv.symm_apply_apply,
    quotEquivMapPowModule_mk]

/-- **The level-`n` quotient of `(M^∧)_𝔮` is a localization of the level-`n` quotient of `M` at
the complement of `𝔭`, over `R` itself.**

The previous result says it is a localization at the image of that complement in `R^∧`;
`IsLocalizedModule.restrictScalars` reads that over `R`, and `levelCompletionEquiv` replaces
`M^∧ ⧸ JⁿM^∧` by `M ⧸ JⁿM`. -/
def levelLocalizationMapCompletion (n : ℕ) :
    (M ⧸ (J ^ n • (⊤ : Submodule R M))) →ₗ[R]
      (Mq ⧸ ((J.map (algebraMap R Rq)) ^ n • (⊤ : Submodule Rq Mq))) :=
  ((levelQuotEquivTower J Rq (Mq := Mq) n).restrictScalars R).toLinearMap ∘ₗ
    ((levelLocalizationMap (J.map (algebraMap R (AdicCompletion J R)))
      (adicPrimeOver J hJp).asIdeal.primeCompl Rq fq n).restrictScalars R ∘ₗ
    (levelCompletionEquiv J hJ n).toLinearMap)

/-- **What `levelLocalizationMapCompletion` does** on the class of `m : M`. -/
@[simp]
theorem levelLocalizationMapCompletion_mk (n : ℕ) (m : M) :
    levelLocalizationMapCompletion J hJ hJp Rq fq n (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (fq (AdicCompletion.of J M m)) := by
  rw [levelLocalizationMapCompletion, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, levelCompletionEquiv_mk]
  rw [show (levelLocalizationMap (J.map (algebraMap R (AdicCompletion J R)))
      (adicPrimeOver J hJp).asIdeal.primeCompl Rq fq n).restrictScalars R
        (Submodule.Quotient.mk (AdicCompletion.of J M m)) =
      Submodule.Quotient.mk (fq (AdicCompletion.of J M m)) from rfl]
  rfl

/-- **`levelLocalizationMapCompletion` is a localization at the complement of `𝔭`.** -/
instance isLocalizedModule_levelLocalizationMapCompletion (n : ℕ) :
    IsLocalizedModule p.primeCompl (levelLocalizationMapCompletion J hJ hJp Rq fq n) := by
  have h := isLocalizedModule_algebraMapSubmonoid_levelLocalizationMap J hJ hJp Rq fq n
  have h' : IsLocalizedModule p.primeCompl
      ((levelLocalizationMap (J.map (algebraMap R (AdicCompletion J R)))
        (adicPrimeOver J hJp).asIdeal.primeCompl Rq fq n).restrictScalars R) :=
    IsLocalizedModule.restrictScalars p.primeCompl _
  have h'' : IsLocalizedModule p.primeCompl
      ((levelLocalizationMap (J.map (algebraMap R (AdicCompletion J R)))
          (adicPrimeOver J hJp).asIdeal.primeCompl Rq fq n).restrictScalars R ∘ₗ
        (levelCompletionEquiv J hJ n).toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right p.primeCompl _ (levelCompletionEquiv J hJ n)
  exact IsLocalizedModule.of_linearEquiv p.primeCompl _
    ((levelQuotEquivTower J Rq (Mq := Mq) n).restrictScalars R)

end ModuleLevel

section Comparison

variable {R : Type u} [CommRing R] (J : Ideal R) {p : Ideal R}
  (hJ : J.FG) [p.IsPrime] (hJp : J ≤ p)
  {M : Type v} [AddCommGroup M] [Module R M]
  (Rp : Type w) [CommRing Rp] [Algebra R Rp] [IsLocalization p.primeCompl Rp]
  {Mp : Type w} [AddCommGroup Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp]
  (fp : M →ₗ[R] Mp) [IsLocalizedModule p.primeCompl fp]
  (Rq : Type w) [CommRing Rq] [Algebra (AdicCompletion J R) Rq] [Algebra R Rq]
    [IsScalarTower R (AdicCompletion J R) Rq]
    [IsLocalization (adicPrimeOver J hJp).asIdeal.primeCompl Rq]
  {Mq : Type w} [AddCommGroup Mq] [Module (AdicCompletion J R) Mq] [Module Rq Mq]
    [Module R Mq] [IsScalarTower (AdicCompletion J R) Rq Mq] [IsScalarTower R Rq Mq]
    [IsScalarTower R (AdicCompletion J R) Mq]
  (fq : AdicCompletion J M →ₗ[AdicCompletion J R] Mq)
    [IsLocalizedModule (adicPrimeOver J hJp).asIdeal.primeCompl fq]

/-- **The level-`n` comparison of the two localized modules.** Both `M_𝔭 ⧸ JⁿM_𝔭` and
`(M^∧)_𝔮 ⧸ Jⁿ(M^∧)_𝔮` are localizations of `M ⧸ JⁿM` at the complement of `𝔭`, so they are
identified, compatibly with the maps from `M ⧸ JⁿM`. -/
def levelModuleEquiv (n : ℕ) :
    (Mp ⧸ ((J.map (algebraMap R Rp)) ^ n • (⊤ : Submodule Rp Mp))) ≃ₗ[R]
      (Mq ⧸ ((J.map (algebraMap R Rq)) ^ n • (⊤ : Submodule Rq Mq))) :=
  IsLocalizedModule.linearEquiv p.primeCompl
    (levelLocalizationMap J p.primeCompl Rp fp n)
    (levelLocalizationMapCompletion J hJ hJp Rq fq n)

/-- **The defining clause of `levelModuleEquiv`**: it matches the two maps from `M ⧸ JⁿM`. -/
@[simp]
theorem levelModuleEquiv_mk (n : ℕ) (m : M) :
    levelModuleEquiv J hJ hJp Rp fp Rq fq n (Submodule.Quotient.mk (fp m)) =
      Submodule.Quotient.mk (fq (AdicCompletion.of J M m)) := by
  have h := IsLocalizedModule.linearEquiv_apply p.primeCompl
    (levelLocalizationMap J p.primeCompl Rp fp n)
    (levelLocalizationMapCompletion J hJ hJp Rq fq n) (Submodule.Quotient.mk m)
  rw [levelLocalizationMap_mk, levelLocalizationMapCompletion_mk] at h
  exact h

/-- **The level comparisons are compatible with the transition maps** of the two towers.

Both sides are `R`-linear maps out of a localization of `M ⧸ JⁿM`, so it is enough that they
agree on the classes coming from `M`, where both are the identity on residue classes. -/
theorem transitionMap_levelModuleEquiv {m n : ℕ} (hmn : m ≤ n)
    (x : Mp ⧸ ((J.map (algebraMap R Rp)) ^ n • (⊤ : Submodule Rp Mp))) :
    AdicCompletion.transitionMap (J.map (algebraMap R Rq)) Mq hmn
        (levelModuleEquiv J hJ hJp Rp fp Rq fq n x) =
      levelModuleEquiv J hJ hJp Rp fp Rq fq m
        (AdicCompletion.transitionMap (J.map (algebraMap R Rp)) Mp hmn x) := by
  have key :
      (AdicCompletion.transitionMap (J.map (algebraMap R Rq)) Mq hmn).restrictScalars R ∘ₗ
          (levelModuleEquiv J hJ hJp Rp fp Rq fq n).toLinearMap =
        (levelModuleEquiv J hJ hJp Rp fp Rq fq m).toLinearMap ∘ₗ
          (AdicCompletion.transitionMap (J.map (algebraMap R Rp)) Mp hmn).restrictScalars R := by
    refine IsLocalizedModule.linearMap_ext p.primeCompl
      (levelLocalizationMap J p.primeCompl Rp fp n)
      (levelLocalizationMapCompletion J hJ hJp Rq fq m) ?_
    refine LinearMap.ext fun y => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [LinearMap.comp_apply, levelLocalizationMap_mk, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply, transitionMap_mk_eq_mk, levelModuleEquiv_mk]
  exact LinearMap.congr_fun key x

/-- **The `J`-adic completion of `M_𝔭` is the `J`-adic completion of `(M^∧)_𝔮`.**

Let `R` be a ring, `J ⊆ R` a finitely generated ideal, `𝔭 ⊇ J` a prime and `M` an `R`-module.
Let `M_𝔭` be a localization of `M` at `𝔭` and let `𝔮` be the prime
`Stacks.Algebraization.adicPrimeOver` of `R^∧` above `𝔭`. Then the `J`-adic completion of `M_𝔭`
is the `J`-adic completion of the localization `(M^∧)_𝔮`.

This lies over the ring comparison
`Stacks.Algebraization.adicCompletionLocalizationAlgEquiv`: both are assembled from the same
correspondence of multiplicative sets, level by level.

Its characterizing clauses are
`Stacks.Algebraization.val_adicCompletionLocalizationAddEquiv`,
`Stacks.Algebraization.adicCompletionLocalizationAddEquiv_of` and
`Stacks.Algebraization.eq_adicCompletionLocalizationAddEquiv_of_val`. -/
def adicCompletionLocalizationAddEquiv :
    AdicCompletion (J.map (algebraMap R Rp)) Mp ≃+
      AdicCompletion (J.map (algebraMap R Rq)) Mq :=
  AdicCompletion.addEquivOfQuotientEquiv _ _
    (fun n => (levelModuleEquiv J hJ hJp Rp fp Rq fq n).toAddEquiv)
    (fun {_ _} hmn x => transitionMap_levelModuleEquiv J hJ hJp Rp fp Rq fq hmn x)

/-- **The defining clause**: the level-`n` component of the comparison is the level-`n`
comparison. -/
@[simp]
theorem val_adicCompletionLocalizationAddEquiv
    (x : AdicCompletion (J.map (algebraMap R Rp)) Mp) (n : ℕ) :
    (adicCompletionLocalizationAddEquiv J hJ hJp Rp fp Rq fq x).val n =
      levelModuleEquiv J hJ hJp Rp fp Rq fq n (x.val n) :=
  rfl

/-- **The comparison on the canonical image of an element of `M_𝔭` coming from `M`.** -/
theorem adicCompletionLocalizationAddEquiv_of (m : M) :
    adicCompletionLocalizationAddEquiv J hJ hJp Rp fp Rq fq
        (AdicCompletion.of (J.map (algebraMap R Rp)) Mp (fp m)) =
      AdicCompletion.of (J.map (algebraMap R Rq)) Mq (fq (AdicCompletion.of J M m)) :=
  AdicCompletion.ext fun n => by
    rw [val_adicCompletionLocalizationAddEquiv]
    exact levelModuleEquiv_mk J hJ hJp Rp fp Rq fq n m

/-- The `n`-th component of the image of `r : R` in the `I`-adic completion of `A` acts on the
level-`n` quotient of a module as `r` does. -/
private theorem val_algebraMap_smul {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] {I : Ideal A} (r : R) (n : ℕ)
    (y : N ⧸ (I ^ n • (⊤ : Submodule A N))) :
    (algebraMap R (AdicCompletion I A) r).val n • y = r • y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (algebraMap R A r • z) = _
  rw [IsScalarTower.algebraMap_smul A, Submodule.Quotient.mk_smul]

/-- **The comparison lies over the ring comparison, on the scalars from the base.** For `r : R`
the comparison carries `r · x` to `r · (the comparison of x)`, the two canonical images of `r`
being matched by `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv_algebraMap`.

This is the module counterpart of the ring comparison being an equivalence of `R`-algebras. -/
theorem adicCompletionLocalizationAddEquiv_algebraMap_smul (r : R)
    (x : AdicCompletion (J.map (algebraMap R Rp)) Mp) :
    adicCompletionLocalizationAddEquiv J hJ hJp Rp fp Rq fq
        (algebraMap R (AdicCompletion (J.map (algebraMap R Rp)) Rp) r • x) =
      algebraMap R (AdicCompletion (J.map (algebraMap R Rq)) Rq) r •
        adicCompletionLocalizationAddEquiv J hJ hJp Rp fp Rq fq x :=
  AdicCompletion.ext fun n => by
    rw [val_adicCompletionLocalizationAddEquiv, AdicCompletion.smul_eval,
      AdicCompletion.smul_eval, val_adicCompletionLocalizationAddEquiv, val_algebraMap_smul,
      val_algebraMap_smul, LinearEquiv.map_smul]

/-- **The defining clause determines the comparison.** -/
theorem eq_adicCompletionLocalizationAddEquiv_of_val
    (F : AdicCompletion (J.map (algebraMap R Rp)) Mp →
      AdicCompletion (J.map (algebraMap R Rq)) Mq)
    (hF : ∀ (n : ℕ) (x : AdicCompletion (J.map (algebraMap R Rp)) Mp),
      (F x).val n = levelModuleEquiv J hJ hJp Rp fp Rq fq n (x.val n))
    (x : AdicCompletion (J.map (algebraMap R Rp)) Mp) :
    F x = adicCompletionLocalizationAddEquiv J hJ hJp Rp fp Rq fq x :=
  AdicCompletion.ext fun n => hF n x

end Comparison

end Stacks.Algebraization

end
