module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.CechModel

/-!
# Local cohomology and direct sums

Let `A` be a commutative ring, `I = (f₁, …, f_r)` a finitely generated ideal, `Y = V(I)` and
`(M_j)_{j ∈ J}` a family of `A`-modules. The descending induction in the proof of
[Stacks, Tag 0DX7] needs the commutation `H^i_Y(⨁_j M_j) = ⨁_j H^i_Y(M_j)`, which does *not*
follow formally from the construction of `RΓ_Y` in
`StacksFrontier/RingTheory/Dualizing/PowerTorsionComparison/LocalCohomologyFunctor.lean`, because
`RΓ_Y` is produced there as a *right* adjoint. (Stacks asserts it "since `RΓ_Y` is a right
adjoint"; the mathematical content is that `RΓ_Y` also happens to be given by a tensor product,
which is what the Čech model supplies.)

This file supplies the missing input, in three layers.

First, the algebraic core: localization commutes with direct sums. The componentwise map
`⨁_j M_j → ⨁_j (M_j)_S` is a localization of `⨁_j M_j` at `S`, because a cocycle condition in a
direct sum involves only finitely many components and the finitely many denominators can be
multiplied together. This gives `(⨁_j M_j)_S ≅ ⨁_j (M_j)_S`, which is the statement the Čech-model
file names as the one thing the library lacked.

Second, the complex-level consequence. Every term of the extended alternating Čech complex
`C^•(f₁, …, f_r; M)` is a direct sum of localizations of `M`, so the previous step plus an
interchange of the two direct sums identifies the degree-`p` term of `C^•(f; ⨁_j M_j)` with
`⨁_j C^p(f; M_j)`, compatibly with the Čech differential; hence
`C^•(f; ⨁_j M_j) ≅ ⨁_j C^•(f; M_j)`.

Third, the vanishing statement local cohomology needs. A cocycle of a direct sum of complexes of
modules has finitely many nonzero components, each of which is a coboundary, so exactness in a
degree is inherited by degreewise direct sums; combined with the Čech model
(`Stacks.LocalCohomology.nonempty_homology_localCohomology_iso_cechHomology`) this gives the
vanishing of `H^i_Y(⨁_j M_j)` from the vanishing of each `H^i_Y(M_j)`.

## Main definitions

* `Stacks.LocalCohomology.directSumMk` — the componentwise localization map
  `⨁_j M_j → ⨁_j (M_j)_S`.
* `Stacks.LocalCohomology.localizedModuleDirectSumEquiv` — the resulting identification
  `(⨁_j M_j)_S ≅ ⨁_j (M_j)_S`.
* `Stacks.LocalCohomology.directSumCommEquiv` — interchange of the two indices of a doubly
  indexed direct sum.
* `Stacks.LocalCohomology.directSumCechComplex` — the degreewise direct sum of the Čech
  complexes of a family of modules.

## Main results

* `Stacks.LocalCohomology.isLocalizedModule_directSumMk` — **localization commutes with direct
  sums**.
* `Stacks.LocalCohomology.cechTermDirectSumEquiv` and
  `Stacks.LocalCohomology.cechComplexDirectSumIso` — **the Čech complex of a direct sum is the
  direct sum of the Čech complexes**.
* `Stacks.LocalCohomology.exactAt_cechComplex_directSum` — exactness in a degree is inherited.
* `Stacks.LocalCohomology.isZero_homology_localCohomology_directSum` — **the local cohomology of
  a direct sum vanishes in a degree as soon as that of every summand does**.

## Implementation notes

The vanishing statement is proved, rather than the isomorphism
`H^i_Y(⨁_j M_j) ≅ ⨁_j H^i_Y(M_j)`, because that is what the induction of Tag 0DX7 consumes and
because the Čech model itself is only available as a `Nonempty` isomorphism, not naturally in the
module. The repository does have `Stacks.Duality.isoCoproductHomologyCochainComplex`, which gives
`Hⁿ(∐_j K_j) ≅ ∐_j Hⁿ(K_j)` at an arbitrary index type; it is not used here because it is stated
for `ℤ`-indexed complexes and for the categorical coproduct, whereas the Čech complex is
`ℕ`-indexed and the comparison above is with `DirectSum`, so the plumbing between the two would
have been longer than the elementwise argument it replaces.

`Stacks.LocalCohomology.cechTermLinearMap` and `Stacks.LocalCohomology.localizedModuleMap_cechι`
are the functoriality of a Čech term in the module, for a plain linear map; they are kept local to
this file rather than taken from a general functoriality statement, since no such statement is in
the library yet.

No `@[stacks 0DX7]` attribute is placed. Two further ingredients of Tag 0DX7 are missing from the
library, and both are named in the report that accompanies this file: the long exact sequence of
`H^i_Y` attached to a short exact sequence of modules (`Dualizing.localCohomologyFunctor` carries
no `CommShift`/`IsTriangulated` structure, so no distinguished triangle is available; through the
Čech model it would instead come from the exactness of localization), and a comparison between
local cohomology computed in `ModuleCat.{u} A` and in `ModuleCat.{max u v} A`, which the two sides
of the equivalence (1) ⇔ (2) of Tag 0DX7 live in.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

universe y w w' v u

namespace Stacks.LocalCohomology

section Localization

variable {R : Type u} [CommRing R] (S : Submonoid R) {J : Type w} (M : J → Type v)
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

/-- The componentwise localization map `⨁ⱼ Mⱼ → ⨁ⱼ (Mⱼ)_S`. -/
abbrev directSumMk : (DirectSum J M) →ₗ[R] DirectSum J fun j => LocalizedModule S (M j) :=
  DirectSum.lmap fun j => LocalizedModule.mkLinearMap S (M j)

/-- Every element of `S` acts invertibly on a direct sum of localizations at `S`. -/
theorem isUnit_algebraMap_directSum (s : S) :
    IsUnit (algebraMap R
      (Module.End R (DirectSum J fun j => LocalizedModule S (M j))) (s : R)) := by
  rw [Module.End.isUnit_iff]
  constructor
  · intro x y hxy
    refine DFinsupp.ext fun j => ?_
    exact ((Module.End.isUnit_iff _).1
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S (M j)) s)).1
      (congrArg (fun z : DirectSum J fun j => LocalizedModule S (M j) => z j) hxy)
  · intro y
    refine ⟨DirectSum.lmap (fun j =>
      ((IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S (M j)) s).unit⁻¹.val)) y, ?_⟩
    refine DFinsupp.ext fun j => ?_
    exact ((Module.End.algebraMap_isUnit_inv_apply_eq_iff (S := R)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S (M j)) s) (y j) _).1 rfl).symm

/-- An element of a direct sum killed by the componentwise localization map is killed by a single
element of `S`: pick a denominator for each of the finitely many nonzero components and multiply
them together. -/
theorem exists_smul_eq_zero_of_directSumMk_eq_zero {x : DirectSum J M}
    (hx : directSumMk S M x = 0) : ∃ c : S, (c : R) • x = 0 := by
  classical
  have hzero : ∀ j, ∃ r ∈ S, r • x j = 0 := fun j =>
    LocalizedModule.mem_ker_mkLinearMap_iff.1
      (congrArg (fun z : DirectSum J fun j => LocalizedModule S (M j) => z j) hx)
  choose g hgS hg using hzero
  refine ⟨⟨∏ j ∈ DFinsupp.support x, g j,
    Submonoid.prod_mem _ fun j _ => hgS j⟩, DFinsupp.ext fun j => ?_⟩
  show (∏ k ∈ DFinsupp.support x, g k) • x j = 0
  by_cases hj : j ∈ DFinsupp.support x
  · rw [← Finset.prod_erase_mul _ _ hj, mul_smul, hg j, smul_zero]
  · rw [DFinsupp.notMem_support_iff.1 hj, smul_zero]

/-- **Localization commutes with direct sums.** The componentwise localization map
`⨁ⱼ Mⱼ → ⨁ⱼ (Mⱼ)_S` exhibits the direct sum of the localizations as the localization of the
direct sum. -/
instance isLocalizedModule_directSumMk : IsLocalizedModule S (directSumMk S M) where
  map_units := isUnit_algebraMap_directSum S M
  surj y := by
    classical
    refine DirectSum.induction_on y ⟨(0, 1), by simp⟩ (fun j z => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
    · obtain ⟨⟨m, t⟩, ht⟩ := IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S (M j)) z
      refine ⟨(DirectSum.lof R J M j m, t), ?_⟩
      change (t : R) • DirectSum.lof R J (fun k => LocalizedModule S (M k)) j z = _
      rw [← map_smul, DirectSum.lmap_lof]
      exact congrArg _ ht
    · obtain ⟨⟨x₁, t₁⟩, ht₁⟩ := h₁
      obtain ⟨⟨x₂, t₂⟩, ht₂⟩ := h₂
      refine ⟨((t₂ : R) • x₁ + (t₁ : R) • x₂, t₁ * t₂), ?_⟩
      change ((t₁ * t₂ : S) : R) • (y₁ + y₂) = _
      rw [map_add, map_smul, map_smul, ← ht₁, ← ht₂]
      change _ • (y₁ + y₂) = (t₂ : R) • ((t₁ : S) • y₁) + (t₁ : R) • ((t₂ : S) • y₂)
      simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_add, smul_smul]
      rw [mul_comm (t₂ : R) (t₁ : R)]
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨c, hc⟩ := exists_smul_eq_zero_of_directSumMk_eq_zero S M
      (x := x₁ - x₂) (by rw [map_sub, h, sub_self])
    exact ⟨c, by rwa [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]⟩

/-- The map on localizations induced by a linear map of modules, as an `R`-linear map. -/
abbrev localizedModuleMap {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (g : N →ₗ[R] P) : LocalizedModule S N →ₗ[R] LocalizedModule S P :=
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N) (LocalizedModule.mkLinearMap S P) g

/-- The map `localizedModuleMap S g` sends the fraction `m / t` to `g m / t`. -/
theorem localizedModuleMap_mk {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (g : N →ₗ[R] P) (m : N) (t : S) :
    localizedModuleMap S g (LocalizedModule.mk m t) = LocalizedModule.mk (g m) t :=
  IsLocalizedModule.map_LocalizedModules S g m t

/-- **Localization commutes with direct sums.** The localization at `S` of a direct sum of
`R`-modules is the direct sum of their localizations. -/
def localizedModuleDirectSumEquiv :
    LocalizedModule S (DirectSum J M) ≃ₗ[R] DirectSum J fun j => LocalizedModule S (M j) :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (DirectSum J M))
    (directSumMk S M)

/-- The identification `localizedModuleDirectSumEquiv S M` sends `x / 1` to `directSumMk S M x`. -/
theorem localizedModuleDirectSumEquiv_mk (x : DirectSum J M) :
    localizedModuleDirectSumEquiv S M (LocalizedModule.mk x 1) = directSumMk S M x :=
  IsLocalizedModule.linearEquiv_apply S _ _ x

/-- The identification of the localization of a direct sum with the direct sum of the
localizations carries the `j`-th summand to the `j`-th summand. -/
theorem localizedModuleDirectSumEquiv_localizedModuleMap_lof [DecidableEq J] (j : J)
    (x : LocalizedModule S (M j)) :
    localizedModuleDirectSumEquiv S M (localizedModuleMap S (DirectSum.lof R J M j) x) =
      DirectSum.lof R J (fun k => LocalizedModule S (M k)) j x := by
  have key : (localizedModuleDirectSumEquiv S M).toLinearMap ∘ₗ
      localizedModuleMap S (DirectSum.lof R J M j) =
      DirectSum.lof R J (fun k => LocalizedModule S (M k)) j := by
    refine IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S (M j))
      (isUnit_algebraMap_directSum S M) (LinearMap.ext fun m => ?_)
    show localizedModuleDirectSumEquiv S M
      (localizedModuleMap S (DirectSum.lof R J M j) (LocalizedModule.mk m 1)) = _
    rw [localizedModuleMap_mk, localizedModuleDirectSumEquiv_mk, DirectSum.lmap_lof]
    rfl
  exact LinearMap.congr_fun key x

section Swap

variable {ι : Type w'} {K : Type w} [DecidableEq ι] [DecidableEq K]
  (N : ι → K → Type y) [∀ i k, AddCommGroup (N i k)] [∀ i k, Module R (N i k)]

/-- Swapping the two summation indices of a doubly indexed direct sum. -/
def directSumCommEquiv :
    (DirectSum ι fun i => DirectSum K fun k => N i k) ≃ₗ[R]
      DirectSum K fun k => DirectSum ι fun i => N i k :=
  LinearEquiv.ofLinearMap
    (DirectSum.toModule R ι _ fun i =>
      DirectSum.lmap fun k => DirectSum.lof R ι (fun i' => N i' k) i)
    (DirectSum.toModule R K _ fun k =>
      DirectSum.lmap fun i => DirectSum.lof R K (fun k' => N i k') k)
    (DirectSum.linearMap_ext R fun k => DirectSum.linearMap_ext R fun i =>
      LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, DirectSum.toModule_lof, DirectSum.lmap_lof,
          LinearMap.id_coe, id_eq])
    (DirectSum.linearMap_ext R fun i => DirectSum.linearMap_ext R fun k =>
      LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, DirectSum.toModule_lof, DirectSum.lmap_lof,
          LinearMap.id_coe, id_eq])

/-- `directSumCommEquiv` sends `x` in the summand indexed by `(i, k)` to `x` in the summand
indexed by `(k, i)`. -/
@[simp] theorem directSumCommEquiv_lof_lof (i : ι) (k : K) (x : N i k) :
    directSumCommEquiv (R := R) N (DirectSum.lof R ι (fun i' => DirectSum K fun k' => N i' k') i
        (DirectSum.lof R K (fun k' => N i k') k x)) =
      DirectSum.lof R K (fun k' => DirectSum ι fun i' => N i' k') k
        (DirectSum.lof R ι (fun i' => N i' k) i x) := by
  simp only [directSumCommEquiv, LinearEquiv.coe_ofLinearMap, DirectSum.toModule_lof,
    DirectSum.lmap_lof]

/-- The inverse of `directSumCommEquiv` sends `x` in the summand indexed by `(k, i)` to `x` in
the summand indexed by `(i, k)`. -/
@[simp] theorem directSumCommEquiv_symm_lof_lof (i : ι) (k : K) (x : N i k) :
    (directSumCommEquiv (R := R) N).symm (DirectSum.lof R K
        (fun k' => DirectSum ι fun i' => N i' k') k
          (DirectSum.lof R ι (fun i' => N i' k) i x)) =
      DirectSum.lof R ι (fun i' => DirectSum K fun k' => N i' k') i
        (DirectSum.lof R K (fun k' => N i k') k x) := by
  rw [LinearEquiv.symm_apply_eq, directSumCommEquiv_lof_lof]

end Swap

end Localization

section Cech

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The map on degree-`p` Čech terms induced by a linear map of modules: localize at each
`∏_{i ∈ s} fᵢ` and take the direct sum over the index sets `s` of cardinality `p`. -/
def cechTermLinearMap {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (g : N →ₗ[R] P) (p : ℕ) : Cech.cechTerm f N p →ₗ[R] Cech.cechTerm f P p :=
  DirectSum.lmap fun s => localizedModuleMap (Cech.cechSub f s.1) g

/-- The transition maps of the Čech complex are natural in the module. -/
theorem localizedModuleMap_cechι {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (g : N →ₗ[R] P) {s t : Finset (Fin r)} (h : s ⊆ t) (x : Cech.cechMod f N s) :
    localizedModuleMap (Cech.cechSub f t) g (Cech.cechι f N h x) =
      Cech.cechι f P h (localizedModuleMap (Cech.cechSub f s) g x) := by
  have key : (localizedModuleMap (Cech.cechSub f t) g).comp (Cech.cechι f N h) =
      (Cech.cechι f P h).comp (localizedModuleMap (Cech.cechSub f s) g) := by
    refine IsLocalizedModule.ext (Cech.cechSub f s)
      (LocalizedModule.mkLinearMap (Cech.cechSub f s) N)
      (fun y => Cech.isUnit_algebraMap f P h
        (LocalizedModule.mkLinearMap (Cech.cechSub f t) P) y)
      (LinearMap.ext fun m => ?_)
    show localizedModuleMap (Cech.cechSub f t) g
      (Cech.cechι f N h (LocalizedModule.mkLinearMap (Cech.cechSub f s) N m)) =
        Cech.cechι f P h (localizedModuleMap (Cech.cechSub f s) g
          (LocalizedModule.mkLinearMap (Cech.cechSub f s) N m))
    rw [Cech.cechι_mk]
    show localizedModuleMap (Cech.cechSub f t) g (LocalizedModule.mk m 1) =
      Cech.cechι f P h (localizedModuleMap (Cech.cechSub f s) g (LocalizedModule.mk m 1))
    rw [localizedModuleMap_mk, localizedModuleMap_mk]
    exact (Cech.cechι_mk f P h (g m)).symm
  exact LinearMap.congr_fun key x

/-- The differential of the Čech complex is natural in the module. -/
theorem cechTermLinearMap_cechD {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P]
    [Module R P] (g : N →ₗ[R] P) (p : ℕ) (x : Cech.cechTerm f N p) :
    cechTermLinearMap f g (p + 1) (Cech.cechD f N p x) =
      Cech.cechD f P p (cechTermLinearMap f g p x) := by
  have key : (cechTermLinearMap f g (p + 1)).comp (Cech.cechD f N p) =
      (Cech.cechD f P p).comp (cechTermLinearMap f g p) := by
    refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun y => ?_
    show cechTermLinearMap f g (p + 1)
        (Cech.cechD f N p (DirectSum.lof R _ (fun t => Cech.cechMod f N t.1) s y)) =
      Cech.cechD f P p (cechTermLinearMap f g p
        (DirectSum.lof R _ (fun t => Cech.cechMod f N t.1) s y))
    simp only [cechTermLinearMap, Cech.cechD_lof, map_sum, map_zsmul, DirectSum.lmap_lof,
      localizedModuleMap_cechι]
  exact LinearMap.congr_fun key x

variable {J : Type (max u v)} [DecidableEq J] (M : J → Type (max u v))
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

/-- **The Čech terms of a direct sum.** In each degree the Čech complex of a direct sum of
modules is the direct sum of the Čech complexes: localization commutes with direct sums, and the
two direct sums — over the index sets `s` and over the family — may be interchanged. -/
def cechTermDirectSumEquiv (p : ℕ) :
    Cech.cechTerm f (DirectSum J M) p ≃ₗ[R] DirectSum J fun j => Cech.cechTerm f (M j) p :=
  (DirectSum.congrLinearEquiv fun s : {s : Finset (Fin r) // s.card = p} =>
      localizedModuleDirectSumEquiv (Cech.cechSub f s.1) M).trans
    (directSumCommEquiv (R := R) fun (s : {s : Finset (Fin r) // s.card = p}) (j : J) =>
      LocalizedModule (Cech.cechSub f s.1) (M j))

/-- The inverse of `cechTermDirectSumEquiv` is, on the `j`-th summand, the map of Čech terms
induced by the inclusion of `M j` into the direct sum. -/
theorem cechTermDirectSumEquiv_symm_lof (p : ℕ) (j : J) (y : Cech.cechTerm f (M j) p) :
    (cechTermDirectSumEquiv f M p).symm
        (DirectSum.lof R J (fun k => Cech.cechTerm f (M k) p) j y) =
      cechTermLinearMap f (DirectSum.lof R J M j) p y := by
  have key : (cechTermDirectSumEquiv f M p).toLinearMap.comp
        (cechTermLinearMap f (DirectSum.lof R J M j) p) =
      DirectSum.lof R J (fun k => Cech.cechTerm f (M k) p) j := by
    refine DirectSum.linearMap_ext R fun s => LinearMap.ext fun x => ?_
    show cechTermDirectSumEquiv f M p (cechTermLinearMap f (DirectSum.lof R J M j) p
        (DirectSum.lof R _ (fun t => Cech.cechMod f (M j) t.1) s x)) = _
    simp only [cechTermDirectSumEquiv, cechTermLinearMap, LinearEquiv.trans_apply,
      DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, LinearEquiv.coe_coe,
      LinearMap.comp_apply, localizedModuleDirectSumEquiv_localizedModuleMap_lof,
      directSumCommEquiv_lof_lof]
  exact (LinearEquiv.symm_apply_eq (cechTermDirectSumEquiv f M p)).2
    (LinearMap.congr_fun key y).symm

/-- The identification of the Čech terms of a direct sum with the direct sum of the Čech terms
is compatible with the Čech differentials. -/
theorem cechD_cechTermDirectSumEquiv_symm (p : ℕ)
    (u : DirectSum J fun j => Cech.cechTerm f (M j) p) :
    Cech.cechD f (DirectSum J M) p ((cechTermDirectSumEquiv f M p).symm u) =
      (cechTermDirectSumEquiv f M (p + 1)).symm
        (DirectSum.lmap (fun j => Cech.cechD f (M j) p) u) := by
  have key : (Cech.cechD f (DirectSum J M) p).comp
        (cechTermDirectSumEquiv f M p).symm.toLinearMap =
      (cechTermDirectSumEquiv f M (p + 1)).symm.toLinearMap.comp
        (DirectSum.lmap fun j => Cech.cechD f (M j) p) := by
    refine DirectSum.linearMap_ext R fun j => LinearMap.ext fun y => ?_
    show Cech.cechD f (DirectSum J M) p ((cechTermDirectSumEquiv f M p).symm
          (DirectSum.lof R J (fun k => Cech.cechTerm f (M k) p) j y)) =
        (cechTermDirectSumEquiv f M (p + 1)).symm
          (DirectSum.lmap (fun k => Cech.cechD f (M k) p)
            (DirectSum.lof R J (fun k => Cech.cechTerm f (M k) p) j y))
    rw [cechTermDirectSumEquiv_symm_lof, DirectSum.lmap_lof,
      cechTermDirectSumEquiv_symm_lof, cechTermLinearMap_cechD]
  exact LinearMap.congr_fun key u

/-- The degreewise direct sum of the Čech complexes of a family of modules. -/
def directSumCechComplex : CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (DirectSum J fun j => Cech.cechTerm f (M j) p))
    (fun p => ModuleCat.ofHom (DirectSum.lmap fun j => Cech.cechD f (M j) p))
    (fun p => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun u => DFinsupp.ext fun j => ?_
      change Cech.cechD f (M j) (p + 1) (Cech.cechD f (M j) p (u j)) = 0
      exact LinearMap.congr_fun (Cech.cechD_comp_cechD f (M j) p) (u j))

/-- **The Čech complex of a direct sum is the direct sum of the Čech complexes.** This is the
complex-level form of the fact that localization commutes with direct sums. -/
def cechComplexDirectSumIso :
    Cech.cechComplex f (DirectSum J M) ≅ directSumCechComplex f M :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun p => (cechTermDirectSumEquiv f M p).symm.toModuleIso)
    (fun p q hpq => by
      obtain rfl : p + 1 = q := hpq
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun u => ?_
      simp only [Cech.cechComplex, directSumCechComplex, CochainComplex.of_d,
        ModuleCat.hom_comp, ModuleCat.hom_ofHom]
      exact cechD_cechTermDirectSumEquiv_symm f M p u)).symm

omit [DecidableEq J] in
/-- The differential of the degreewise direct sum acts componentwise. -/
theorem directSumCechComplex_d_eq (p q : ℕ) :
    ((directSumCechComplex f M).d p q).hom =
      DirectSum.lmap fun j => ((Cech.cechComplex f (M j)).d p q).hom := by
  by_cases hpq : (ComplexShape.up ℕ).Rel p q
  · obtain rfl : p + 1 = q := hpq
    simp only [directSumCechComplex, Cech.cechComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
    rfl
  · have h0 : ∀ k : J, ((Cech.cechComplex f (M k)).d p q).hom = 0 := fun k => by
      rw [HomologicalComplex.shape _ _ _ hpq, ModuleCat.hom_zero]
    rw [HomologicalComplex.shape _ _ _ hpq, ModuleCat.hom_zero]
    refine LinearMap.ext fun u => DFinsupp.ext fun j => ?_
    simp only [h0]
    rfl

omit [DecidableEq J] in
/-- **Exactness passes to degreewise direct sums.** A cocycle of the direct sum has finitely many
nonzero components, each of which is a coboundary; taking the chosen primitives on the support and
zero elsewhere produces a primitive in the direct sum. -/
theorem exactAt_directSumCechComplex (n : ℕ)
    (h : ∀ j, (Cech.cechComplex f (M j)).ExactAt n) :
    (directSumCechComplex f M).ExactAt n := by
  classical
  have main : ∀ u : DirectSum J fun k => Cech.cechTerm f (M k) n,
      ((directSumCechComplex f M).d n ((ComplexShape.up ℕ).next n)).hom u = 0 →
        ∃ v : DirectSum J fun k =>
            Cech.cechTerm f (M k) ((ComplexShape.up ℕ).prev n),
          ((directSumCechComplex f M).d ((ComplexShape.up ℕ).prev n) n).hom v = u := by
    intro u hu
    have hug : ∀ j,
        ((Cech.cechComplex f (M j)).d n ((ComplexShape.up ℕ).next n)).hom (u j) = 0 := by
      intro j
      have hu' : (DirectSum.lmap fun k =>
            ((Cech.cechComplex f (M k)).d n ((ComplexShape.up ℕ).next n)).hom) u = 0 :=
        (LinearMap.congr_fun
          (directSumCechComplex_d_eq f M n ((ComplexShape.up ℕ).next n)) u).symm.trans hu
      exact congrArg (fun z => z j) hu'
    have hex : ∀ j, ∃ v : Cech.cechTerm f (M j) ((ComplexShape.up ℕ).prev n),
        ((Cech.cechComplex f (M j)).d ((ComplexShape.up ℕ).prev n) n).hom v = u j := by
      intro j
      obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).1 (h j) (u j) (hug j)
      exact ⟨v, hv⟩
    choose w hw using hex
    set W : DirectSum J fun k => Cech.cechTerm f (M k) ((ComplexShape.up ℕ).prev n) :=
      DFinsupp.mk (DFinsupp.support u) fun j => w j.1 with hW
    refine ⟨W, ?_⟩
    have step : (DirectSum.lmap fun k =>
        ((Cech.cechComplex f (M k)).d ((ComplexShape.up ℕ).prev n) n).hom) W = u := by
      refine DFinsupp.ext fun j => ?_
      show ((Cech.cechComplex f (M j)).d ((ComplexShape.up ℕ).prev n) n).hom (W j) = u j
      by_cases hj : j ∈ DFinsupp.support u
      · rw [hW, DFinsupp.mk_apply, dite_eq_left hj]
        exact hw j
      · rw [hW, DFinsupp.mk_apply, dite_eq_right hj, DFinsupp.notMem_support_iff.1 hj]
        exact map_zero _
    exact (LinearMap.congr_fun
      (directSumCechComplex_d_eq f M ((ComplexShape.up ℕ).prev n) n) W).trans step
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  exact main

omit [DecidableEq J] in
/-- The Čech complex of a direct sum of modules is exact in a degree as soon as the Čech complex
of each summand is. -/
theorem exactAt_cechComplex_directSum (n : ℕ)
    (h : ∀ j, (Cech.cechComplex f (M j)).ExactAt n) :
    (Cech.cechComplex f (DirectSum J M)).ExactAt n := by
  classical
  exact (exactAt_directSumCechComplex f M n h).of_iso (cechComplexDirectSumIso f M).symm

omit [DecidableEq J] in
/-- **The local cohomology of a direct sum.** If the local cohomology of each `M j` supported on
`V(I)` vanishes in degree `i`, then so does the local cohomology of `⨁ⱼ Mⱼ`.

This is the input the descending induction of [Stacks, Tag 0DX7] needs, and the reason it is not
formal is that `RΓ_{V(I)}` is a *right* adjoint. It is obtained here from the Čech model of
`StacksFrontier/RingTheory/LocalCohomology/CechModel.lean`: `H^i_{V(I)}(N)` is the `i`-th cohomology
of `C^•(f₁, …, f_r; N)`, and that complex turns a direct sum of modules into the degreewise direct
sum of the complexes, because localization does. -/
theorem isZero_homology_localCohomology_directSum
    (I : Ideal R) (hI : I.FG) (hIf : Ideal.span (Set.range f) = I) (i : ℤ)
    (h : ∀ j, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
            (ModuleCat.of R (M j))))))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((Dualizing.derivedPowerTorsionProperty R I hI).ι.obj
        ((Dualizing.localCohomologyFunctor R I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
            (ModuleCat.of R (DirectSum J M)))))) := by
  classical
  obtain ⟨e⟩ := nonempty_homology_localCohomology_iso_cechHomology f
    (ModuleCat.of R (DirectSum J M)) I hI hIf i
  refine IsZero.of_iso ?_ e
  rcases lt_or_ge i 0 with hneg | hpos
  · exact (HomologicalComplex.ExactAt.of_isZero
      (isZero_extendedCechComplex_X f (ModuleCat.of R (DirectSum J M)) i
        (Or.inl hneg))).isZero_homology
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    have hsum : ∀ j, (Cech.cechComplex f (M j)).ExactAt n := by
      intro j
      obtain ⟨ej⟩ := nonempty_homology_localCohomology_iso_cechHomology f
        (ModuleCat.of R (M j)) I hI hIf (n : ℤ)
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact IsZero.of_iso (IsZero.of_iso (h j) ej.symm)
        (HomologicalComplex.extendHomologyIso (Cech.cechComplex f (M j))
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)).symm
    refine IsZero.of_iso ?_ (HomologicalComplex.extendHomologyIso
      (Cech.cechComplex f (DirectSum J M)) ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) (by simp))
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact exactAt_cechComplex_directSum f M n hsum

end Cech

end Stacks.LocalCohomology

end
