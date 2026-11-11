module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.Algebra.Homology.Eta
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway

/-!
# The cohomology of the décalage complex at a single element

Fix a commutative ring `A` and an element `f ∈ A`. An `A`-module `M` is `f`-torsion free if `f`
is a nonzerodivisor on `M` (i.e. `f • x = 0 → x = 0`, encoded as `IsSMulRegular M f`). For such a
module the localization map `M → M_f` is injective, and inside `M_f` one has, for every `i ∈ ℤ`,
the submodule `f^i M := { f^i x | x ∈ M }`.

Given a cochain complex `M^•` of `f`-torsion free `A`-modules (`d^i : M^i → M^{i+1}` with
`d^{i+1} ∘ d^i = 0`), the Berthelot–Ogus décalage complex `η_f M^•` is defined termwise inside
the localizations by
  `(η_f M)^i := { x ∈ f^i M^i | d^i x ∈ f^{i+1} M^{i+1} } ⊆ M^i_f`,
with the differential the restriction of the localized `d^i`.

## Main results

* `Stacks.Decalage.Cohomology.etaCohomologyMap`: multiplication by `f^i`, `[z] ↦ [f^i z]`, as an
  `A`-linear map `H^i(M^•) → H^i(η_f M^•)`. It is surjective
  (`Stacks.Decalage.Cohomology.etaCohomologyMap_surjective`) and its kernel is exactly the
  `f`-torsion submodule `H^i(M^•)[f]` (`Stacks.Decalage.Cohomology.etaCohomologyMap_eq_zero_iff`).
* `Stacks.Decalage.Cohomology.bijective_etaCohomologyTorsionMap`: hence the canonical map
  `Stacks.Decalage.Cohomology.etaCohomologyTorsionMap : H^i(M^•) / H^i(M^•)[f] → H^i(η_f M^•)`,
  `[z] ↦ [f^i z]`, is an isomorphism (Stacks Tag 0F7P).

## Implementation notes

No hypothesis `f ∈ nonZeroDivisors A` is needed: everything is proved from the termwise
`f`-torsion-freeness of the complex (`Stacks.Decalage.Cohomology.FTFComplex.tf`), which is what
the kernel computation cancels with.

## References

* [Stacks Project, Tag 0F7P](https://stacks.math.columbia.edu/tag/0F7P)
-/

@[expose] public section

/-! ## The décalage at the powers of a single element

`EtaPow` specializes the décalage submodules `Eta.zsmulSub` and `Eta.etaTerm` to the
submonoid `Submonoid.powers f` and to the unit of `A_f` given by `f`: the submodules
`f^i M ⊆ M_f` and the degree-`i` décalage term of an `A`-linear map. -/

namespace EtaPow

variable {A : Type*} [CommRing A]

/-- The localization map `M → M_f`. -/
noncomputable def toLoc (f : A) (M : Type*) [AddCommGroup M] [Module A M] :
    M →ₗ[A] LocalizedModule.Away f M :=
  LocalizedModule.mkLinearMap (Submonoid.powers f) M

/-- The localized extension `M_f → N_f` of an `A`-linear map `d : M → N`: `Eta.locMap` at the
submonoid of powers of `f`. -/
noncomputable abbrev fLoc (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) :
    LocalizedModule.Away f M →ₗ[A] LocalizedModule.Away f N :=
  Eta.locMap (Submonoid.powers f) d

/-- Multiplication by `f^i` after the localization map: the `A`-linear map `M → M_f`,
`x ↦ f^i • ι x`, whose range is the submodule `f^i M`. -/
noncomputable def fpowMap (f : A) (M : Type*) [AddCommGroup M] [Module A M] (i : ℤ) :
    M →ₗ[A] LocalizedModule.Away f M :=
  (Eta.zpowEquiv (Submonoid.powers f) M (Stacks.GradedLaurent.awayUnit f) i).toLinearMap ∘ₗ
    toLoc f M

/-- The submodule `f^i M ⊆ M_f`, the image of `M` under multiplication by the `i`-th power
of the unit `f` (for `i < 0` this uses that `f` is invertible in `M_f`). -/
noncomputable def fpowSub (f : A) (M : Type*) [AddCommGroup M] [Module A M] (i : ℤ) :
    Submodule A (LocalizedModule.Away f M) :=
  Eta.zsmulSub (Submonoid.powers f) (Stacks.GradedLaurent.awayUnit f) i
    (LinearMap.range (toLoc f M))

/-- The degree-`i` term of the décalage of an `A`-linear map `d : M → N` with respect to
`f`:  `{ x ∈ f^i M | d x ∈ f^{i+1} N } ⊆ M_f`, with `d` extended to the localizations. -/
noncomputable def fetaTerm (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) (i : ℤ) :
    Submodule A (LocalizedModule.Away f M) :=
  Eta.etaTerm (Submonoid.powers f) (Stacks.GradedLaurent.awayUnit f) d i
    (LinearMap.range (toLoc f M)) (LinearMap.range (toLoc f N))

section Lemmas

variable {f : A} {M N K : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup K] [Module A K]

/-- The localization map sends `x` to the fraction `x / 1`. -/
theorem toLoc_apply (x : M) : toLoc f M x = LocalizedModule.mk x 1 := rfl

/-- `fpowMap f M i` sends `m` to `f^i • ι m`. -/
theorem fpowMap_apply (i : ℤ) (m : M) :
    fpowMap f M i m = (Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f M m := rfl

/-- The unit `Stacks.GradedLaurent.awayUnit f` of `A_f` is the image of `f` under the algebra
map. -/
theorem fUnit_val :
    ((Stacks.GradedLaurent.awayUnit f : (Localization.Away f)ˣ) : Localization.Away f) =
      algebraMap A (Localization.Away f) f :=
  IsUnit.unit_spec _

/-- The unit `f` of `A_f` acts on `M_f` by the `A`-scalar `f`. -/
@[simp]
theorem fUnit_smul (x : LocalizedModule.Away f M) :
    (Stacks.GradedLaurent.awayUnit f : Localization.Away f) • x = f • x := by
  rw [fUnit_val]
  exact algebraMap_smul (Localization.Away f) f x

/-- Multiplication by `f^i` composes: `f^i • (f^j • x) = f^{i+j} • x`. -/
theorem fUnit_zpow_smul_smul (i j : ℤ) (x : LocalizedModule.Away f M) :
    (Stacks.GradedLaurent.awayUnit f ^ i) • ((Stacks.GradedLaurent.awayUnit f ^ j) • x) =
      (Stacks.GradedLaurent.awayUnit f ^ (i + j)) • x := by
  rw [smul_smul, zpow_add]

/-- Multiplication by `f^i` is injective on `M_f`, hence can be cancelled. -/
theorem fUnit_zpow_smul_left_cancel (i : ℤ) {x y : LocalizedModule.Away f M}
    (h : (Stacks.GradedLaurent.awayUnit f ^ i) • x = (Stacks.GradedLaurent.awayUnit f ^ i) • y) :
    x = y :=
  Eta.zpowEquiv_injective (Submonoid.powers f) (Stacks.GradedLaurent.awayUnit f) i h

/-- Multiplication by `f^i` kills only `0`. -/
@[simp]
theorem fUnit_zpow_smul_eq_zero_iff (i : ℤ) (x : LocalizedModule.Away f M) :
    (Stacks.GradedLaurent.awayUnit f ^ i) • x = 0 ↔ x = 0 :=
  (Eta.zpowEquiv (Submonoid.powers f) M (Stacks.GradedLaurent.awayUnit f) i).map_eq_zero_iff

/-- Multiplication by `f` on a localized element is multiplication by `f` upstairs. -/
theorem fUnit_zpow_one_smul_toLoc (m : M) :
    (Stacks.GradedLaurent.awayUnit f ^ (1 : ℤ)) • toLoc f M m = toLoc f M (f • m) := by
  rw [zpow_one, Units.smul_def, fUnit_smul, map_smul]

/-- Moving a factor `f` across the localization map shifts the exponent: `f^i • ι (f • m)` is
`f^{i+1} • ι m`. -/
private theorem fUnit_zpow_smul_toLoc_smul (i : ℤ) (m : M) :
    (Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f M (f • m) =
      (Stacks.GradedLaurent.awayUnit f ^ (i + 1)) • toLoc f M m := by
  rw [← fUnit_zpow_one_smul_toLoc, fUnit_zpow_smul_smul]

/-- The localized map on the image of the localization map. -/
@[simp]
theorem fLoc_toLoc (d : M →ₗ[A] N) (x : M) : fLoc f d (toLoc f M x) = toLoc f N (d x) :=
  Eta.locMap_mkLinearMap (Submonoid.powers f) d x

/-- The localized map commutes with multiplication by `f^i`. -/
theorem fLoc_zpow_smul (d : M →ₗ[A] N) (i : ℤ) (x : LocalizedModule.Away f M) :
    fLoc f d ((Stacks.GradedLaurent.awayUnit f ^ i) • x) =
      (Stacks.GradedLaurent.awayUnit f ^ i) • fLoc f d x :=
  Eta.locMap_units_smul (Submonoid.powers f) d (Stacks.GradedLaurent.awayUnit f ^ i) x

/-- `f^i M` is the range of `x ↦ f^i • ι x`. -/
theorem fpowSub_eq_range (i : ℤ) : fpowSub f M i = LinearMap.range (fpowMap f M i) :=
  Eta.zsmulSub_range (Submonoid.powers f) (toLoc f M) (Stacks.GradedLaurent.awayUnit f) i

/-- Membership in `f^i M`. -/
theorem mem_fpowSub {i : ℤ} {x : LocalizedModule.Away f M} :
    x ∈ fpowSub f M i ↔ ∃ m : M, (Stacks.GradedLaurent.awayUnit f ^ i) • toLoc f M m = x := by
  rw [fpowSub, Eta.mem_zsmulSub]
  constructor
  · rintro ⟨y, ⟨m, rfl⟩, rfl⟩; exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩; exact ⟨toLoc f M m, ⟨m, rfl⟩, rfl⟩

/-- The degree-`i` décalage term as an intersection. -/
theorem fetaTerm_eq_inf (d : M →ₗ[A] N) (i : ℤ) :
    fetaTerm f d i = fpowSub f M i ⊓ (fpowSub f N (i + 1)).comap (fLoc f d) := rfl

/-- Membership in the degree-`i` décalage term. -/
theorem mem_fetaTerm {d : M →ₗ[A] N} {i : ℤ} {x : LocalizedModule.Away f M} :
    x ∈ fetaTerm f d i ↔ x ∈ fpowSub f M i ∧ fLoc f d x ∈ fpowSub f N (i + 1) :=
  Iff.rfl

/-- An element of the degree-`i` décalage term lies in `f^i M`. -/
theorem mem_fpowSub_of_mem_fetaTerm {d : M →ₗ[A] N} {i : ℤ} {x : LocalizedModule.Away f M}
    (hx : x ∈ fetaTerm f d i) : x ∈ fpowSub f M i :=
  (mem_fetaTerm.mp hx).left

/-- **The décalage of a complex is a complex.** If `e ∘ₗ d = 0`, the localized `d` carries the
degree-`i` décalage term of `d` into the degree-`(i+1)` décalage term of `e`. -/
theorem fLoc_mem_fetaTerm {d : M →ₗ[A] N} {e : N →ₗ[A] K} (h : e ∘ₗ d = 0) (i : ℤ)
    {x : LocalizedModule.Away f M} (hx : x ∈ fetaTerm f d i) : fLoc f d x ∈ fetaTerm f e (i + 1) :=
  Eta.locMap_etaTerm_mem (Submonoid.powers f) (Stacks.GradedLaurent.awayUnit f) d e h i _ _ _ hx

/-- The localization map is injective on modules on which `f` acts regularly. -/
theorem toLoc_injective_of_isSMulRegular (htf : IsSMulRegular M f) :
    Function.Injective (toLoc f M) :=
  (IsLocalizedModule.injective_iff_isRegular (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)).mpr fun ⟨_, n, hn⟩ x y hxy => by
      simp only [Submonoid.smul_def, ← hn] at hxy
      exact htf.pow n hxy

end Lemmas

end EtaPow

/-! ## Main Definitions -/

namespace Stacks.Decalage.Cohomology

open EtaPow

variable {A : Type*} [CommRing A]

/-- A cochain complex of `f`-torsion free `A`-modules: a `ℤ`-indexed family of
`A`-modules `M i` with differentials `d i : M i → M (i + 1)` satisfying
`d (i + 1) ∘ d i = 0`, on each of which `f` acts regularly. -/
structure FTFComplex (A : Type*) [CommRing A] (f : A) where
  /-- The terms `M^i` of the complex. -/
  M : ℤ → Type*
  [grp : ∀ i, AddCommGroup (M i)]
  [mod : ∀ i, Module A (M i)]
  /-- The differentials `d^i : M^i →ₗ M^{i+1}`. -/
  d : ∀ i, M i →ₗ[A] M (i + 1)
  /-- The cochain condition `d^{i+1} ∘ d^i = 0`. -/
  d_comp_d : ∀ i, (d (i + 1)).comp (d i) = 0
  /-- Each `M^i` is `f`-torsion free. -/
  tf : ∀ i, IsSMulRegular (M i) f

attribute [instance] FTFComplex.grp FTFComplex.mod

variable {f : A}

/-- The localized differential `d^i : M^i_f → M^{i+1}_f`. -/
noncomputable def locD (C : FTFComplex A f) (i : ℤ) :
    LocalizedModule.Away f (C.M i) →ₗ[A] LocalizedModule.Away f (C.M (i + 1)) :=
  fLoc f (C.d i)

/-! ## Cohomology

The cohomology is recorded with a one-step shift: `Hcohom C j` is the cohomology
`H^{j+1}` at position `j + 1`.  This avoids `ℤ`-index offset casts
(`(j-1)+1` vs `j`) and is harmless since `j` ranges over all of `ℤ`. -/

/-- `Z^{j+1}(M^•) = ker(d^{j+1})`, the cocycles at position `j+1`. -/
noncomputable abbrev Zc (C : FTFComplex A f) (j : ℤ) : Submodule A (C.M (j + 1)) :=
  LinearMap.ker (C.d (j + 1))

/-- `B^{j+1}(M^•) = im(d^j)`, the coboundaries at position `j+1`. -/
noncomputable abbrev Bc (C : FTFComplex A f) (j : ℤ) : Submodule A (C.M (j + 1)) :=
  LinearMap.range (C.d j)

/-- The cohomology `H^{j+1}(M^•) = Z^{j+1}/B^{j+1}`. -/
noncomputable abbrev Hcohom (C : FTFComplex A f) (j : ℤ) :=
  (Zc C j) ⧸ (Bc C j).submoduleOf (Zc C j)

/-- `Z^{j+1}(η_f M^•)`: the cocycles of the décalage complex at position `j+1`,
i.e. the elements of `(η_f M)^{j+1}` killed by the (localized) differential. -/
noncomputable abbrev Zeta (C : FTFComplex A f) (j : ℤ) :
    Submodule A (LocalizedModule.Away f (C.M (j + 1))) :=
  fetaTerm f (C.d (j + 1)) (j + 1) ⊓ LinearMap.ker (locD C (j + 1))

/-- `B^{j+1}(η_f M^•)`: the coboundaries of the décalage complex at position
`j+1`, i.e. the image of `(η_f M)^j` under the (localized) differential. -/
noncomputable abbrev Beta (C : FTFComplex A f) (j : ℤ) :
    Submodule A (LocalizedModule.Away f (C.M (j + 1))) :=
  Submodule.map (locD C j) (fetaTerm f (C.d j) j)

/-- The cohomology `H^{j+1}(η_f M^•) = Z^{j+1}(η_f M^•)/B^{j+1}(η_f M^•)`. -/
noncomputable abbrev Heta (C : FTFComplex A f) (j : ℤ) :=
  (Zeta C j) ⧸ (Beta C j).submoduleOf (Zeta C j)

/-- The `A`-linear map `z ↦ f^{j+1} • z` from the cocycles `Z^{j+1}(M^•)`
into the localization `M^{j+1}_f`.  This is the underlying map of the
multiplication-by-`f^{j+1}` homomorphism `Φ^{j+1}`. -/
noncomputable def fpowZ (C : FTFComplex A f) (j : ℤ) :
    Zc C j →ₗ[A] LocalizedModule.Away f (C.M (j + 1)) :=
  (fpowMap f (C.M (j + 1)) (j + 1)).comp (Zc C j).subtype

/-! ## Lemmas about `fpowSub`, `locD`, `fetaTerm` -/

section Complex

variable (C : FTFComplex A f)

/-- Membership in the degree-`i` décalage term of the complex. -/
theorem mem_fetaTerm_locD {i : ℤ} {x : LocalizedModule.Away f (C.M i)} :
    x ∈ fetaTerm f (C.d i) i ↔
      x ∈ fpowSub f (C.M i) i ∧ locD C i x ∈ fpowSub f (C.M (i + 1)) (i + 1) :=
  Iff.rfl

/-- The localized differential restricts to `d^i` on the image of the localization map. -/
@[simp]
theorem locD_toLoc (i : ℤ) (x : C.M i) :
    locD C i (toLoc f (C.M i) x) = toLoc f (C.M (i + 1)) (C.d i x) :=
  fLoc_toLoc (C.d i) x

/-- The localized differential commutes with multiplication by `f^k`. -/
theorem locD_zpow_smul (i k : ℤ) (x : LocalizedModule.Away f (C.M i)) :
    locD C i ((Stacks.GradedLaurent.awayUnit f ^ k) • x) =
      (Stacks.GradedLaurent.awayUnit f ^ k) • locD C i x :=
  fLoc_zpow_smul (C.d i) k x

/-- Membership in the cocycles of the décalage complex. -/
theorem mem_etaCocycles {j : ℤ} {x : LocalizedModule.Away f (C.M (j + 1))} :
    x ∈ Zeta C j ↔
      x ∈ fetaTerm f (C.d (j + 1)) (j + 1) ∧ locD C (j + 1) x = 0 :=
  Iff.rfl

/-- A cocycle is killed by the differential. -/
theorem d_eq_zero_of_mem_cocycles {j : ℤ} {z : C.M (j + 1)} (hz : z ∈ Zc C j) :
    C.d (j + 1) z = 0 := LinearMap.mem_ker.mp hz

/-- An `η_f`-cocycle lies in the degree-`(j+1)` décalage term. -/
theorem mem_fetaTerm_of_mem_etaCocycles {j : ℤ} {x : LocalizedModule.Away f (C.M (j + 1))}
    (hx : x ∈ Zeta C j) : x ∈ fetaTerm f (C.d (j + 1)) (j + 1) :=
  ((mem_etaCocycles C).mp hx).left

/-- An `η_f`-cocycle is killed by the localized differential. -/
theorem locD_eq_zero_of_mem_etaCocycles {j : ℤ} {x : LocalizedModule.Away f (C.M (j + 1))}
    (hx : x ∈ Zeta C j) : locD C (j + 1) x = 0 :=
  ((mem_etaCocycles C).mp hx).right

/-- `fpowZ C j` sends a cocycle `z` to `f^{j+1} • ι z`. -/
theorem fpowZ_apply (j : ℤ) (z : Zc C j) :
    fpowZ C j z =
      (Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.M (j + 1)) (z : C.M (j + 1)) :=
  rfl

/-- `f^{j+1} z` (for `z` a cocycle) lies in `Zeta`. -/
theorem fpowZ_mem_Zeta (j : ℤ) (z : Zc C j) :
    fpowZ C j z ∈ Zeta C j := by
  have hkey : locD C (j + 1) (fpowZ C j z) = 0 := by
    rw [fpowZ_apply, locD_zpow_smul, locD_toLoc, d_eq_zero_of_mem_cocycles C z.property,
      map_zero, smul_zero]
  exact (mem_etaCocycles C).mpr
    ⟨(mem_fetaTerm_locD C).mpr ⟨mem_fpowSub.mpr ⟨z, rfl⟩, hkey ▸ Submodule.zero_mem _⟩, hkey⟩

/-- For a coboundary `z = d^j w`, `f^{j+1} z` lies in `Beta`. -/
theorem fpow_coboundary_mem_Beta (j : ℤ) (w : C.M j) :
    (Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.M (j + 1)) (C.d j w) ∈ Beta C j := by
  set η : LocalizedModule.Away f (C.M j) :=
    (Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.M j) w with hη
  have hη1 : η ∈ fpowSub f (C.M j) j := mem_fpowSub.mpr ⟨f • w, fUnit_zpow_smul_toLoc_smul j w⟩
  have hlocD : locD C j η =
      (Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.M (j + 1)) (C.d j w) := by
    rw [hη, locD_zpow_smul, locD_toLoc]
  have hη2 : locD C j η ∈ fpowSub f (C.M (j + 1)) (j + 1) := by
    rw [hlocD, mem_fpowSub]
    exact ⟨C.d j w, rfl⟩
  have hηeta : η ∈ fetaTerm f (C.d j) j := (mem_fetaTerm_locD C).mpr ⟨hη1, hη2⟩
  rw [Beta, ← hlocD]
  exact Submodule.mem_map_of_mem hηeta

/-- If `d^j w = f • m`, then `f^j ι(w) ∈ (η_f M)^j`. -/
theorem fpow_toLoc_mem_fetaTerm (j : ℤ) (w : C.M j) {m : C.M (j + 1)}
    (hdiv : C.d j w = f • m) :
    (Stacks.GradedLaurent.awayUnit f ^ j) • toLoc f (C.M j) w ∈ fetaTerm f (C.d j) j := by
  refine (mem_fetaTerm_locD C).mpr ⟨mem_fpowSub.mpr ⟨w, rfl⟩, ?_⟩
  rw [locD_zpow_smul, locD_toLoc, mem_fpowSub]
  exact ⟨m, by rw [hdiv, fUnit_zpow_smul_toLoc_smul]⟩

/-- `f^{j+1} z` is an `η_f`-coboundary iff `f • z` is a coboundary. -/
theorem fpowZ_mem_Beta_iff (j : ℤ) (z : Zc C j) :
    fpowZ C j z ∈ Beta C j ↔ f • (z : C.M (j + 1)) ∈ Bc C j := by
  constructor
  · rintro ⟨η, hηeta, hηeq⟩
    obtain ⟨w, hw⟩ := mem_fpowSub.mp (mem_fpowSub_of_mem_fetaTerm hηeta)
    rw [← hw, locD_zpow_smul, locD_toLoc, fpowZ_apply,
      ← fUnit_zpow_smul_toLoc_smul] at hηeq
    exact ⟨w, toLoc_injective_of_isSMulRegular (C.tf (j + 1))
      (fUnit_zpow_smul_left_cancel j hηeq)⟩
  · rintro ⟨w, hw⟩
    rw [Beta, Submodule.mem_map]
    refine ⟨(Stacks.GradedLaurent.awayUnit f ^ j) • toLoc f (C.M j) w,
      fpow_toLoc_mem_fetaTerm C j w hw, ?_⟩
    rw [locD_zpow_smul, locD_toLoc, hw, fUnit_zpow_smul_toLoc_smul, fpowZ_apply]

/-- Every `η_f`-cocycle in degree `j + 1` is `f^{j+1}` times a cocycle. -/
theorem exists_fpowZ_eq (j : ℤ) (ζ : Zeta C j) :
    ∃ z : Zc C j, fpowZ C j z = ζ := by
  obtain ⟨m, hm⟩ :=
    mem_fpowSub.mp (mem_fpowSub_of_mem_fetaTerm (mem_fetaTerm_of_mem_etaCocycles C ζ.property))
  have hdm0 : locD C (j + 1)
      ((Stacks.GradedLaurent.awayUnit f ^ (j + 1)) • toLoc f (C.M (j + 1)) m) = 0 := by
    rw [hm]
    exact locD_eq_zero_of_mem_etaCocycles C ζ.property
  rw [locD_zpow_smul, locD_toLoc, fUnit_zpow_smul_eq_zero_iff] at hdm0
  exact ⟨⟨m, toLoc_injective_of_isSMulRegular (C.tf (j + 1 + 1))
      (by rw [hdm0]; simp [toLoc_apply])⟩,
    by rw [fpowZ_apply, hm]⟩

/-! ## Multiplication by `f^{j+1}` on cohomology -/

/-- Multiplication by `f^{j+1}` as an `A`-linear map `H^{j+1}(M^•) → H^{j+1}(η_f M^•)`. -/
noncomputable def etaCohomologyMap (j : ℤ) : Hcohom C j →ₗ[A] Heta C j :=
  ((Bc C j).submoduleOf (Zc C j)).liftQ
    (((Beta C j).submoduleOf (Zeta C j)).mkQ.comp
      ((fpowZ C j).codRestrict (Zeta C j) (fpowZ_mem_Zeta C j))) <| by
    rintro z ⟨w, hw⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
    change fpowZ C j z ∈ Beta C j
    rw [fpowZ_apply, ← Submodule.subtype_apply, ← hw]
    exact fpow_coboundary_mem_Beta C j w

/-- Multiplication by `f^{j+1}` sends the class of a cocycle `z` to the class of
`f^{j+1} • z`. -/
@[simp]
theorem etaCohomologyMap_mk (j : ℤ) (z : Zc C j) :
    etaCohomologyMap C j (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (⟨fpowZ C j z, fpowZ_mem_Zeta C j z⟩ : Zeta C j) :=
  rfl

/-- Multiplication by `f^{j+1}` is surjective onto `H^{j+1}(η_f M^•)`. -/
theorem etaCohomologyMap_surjective (j : ℤ) : Function.Surjective (etaCohomologyMap C j) := by
  intro ξ
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  obtain ⟨z, hz⟩ := exists_fpowZ_eq C j ζ
  exact ⟨Submodule.Quotient.mk z, congrArg Submodule.Quotient.mk (Subtype.ext hz)⟩

/-- The kernel of multiplication by `f^{j+1}` is the `f`-torsion of `H^{j+1}(M^•)`. -/
theorem etaCohomologyMap_eq_zero_iff (j : ℤ) (ξ : Hcohom C j) :
    etaCohomologyMap C j ξ = 0 ↔ f • ξ = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [etaCohomologyMap_mk, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf,
    Submodule.mem_comap]
  simp only [Submodule.subtype_apply]
  rw [fpowZ_mem_Beta_iff, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
  simp only [Submodule.subtype_apply, SetLike.val_smul]

/-- The canonical isomorphism `H^{j+1}(M^•) / H^{j+1}(M^•)[f] ≅ H^{j+1}(η_f M^•)` induced by
multiplication by `f^{j+1}`. -/
noncomputable def etaCohomologyEquiv (j : ℤ) :
    (Hcohom C j ⧸ LinearMap.ker (etaCohomologyMap C j)) ≃ₗ[A] Heta C j :=
  (etaCohomologyMap C j).quotKerEquivOfSurjective (etaCohomologyMap_surjective C j)

/-- The isomorphism `etaCohomologyEquiv` sends the class of `ξ` to `etaCohomologyMap C j ξ`. -/
@[simp]
theorem etaCohomologyEquiv_mk (j : ℤ) (ξ : Hcohom C j) :
    etaCohomologyEquiv C j (Submodule.Quotient.mk ξ) = etaCohomologyMap C j ξ :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ ξ

/-- Membership in the kernel of multiplication by `f^{j+1}` is `f`-torsion. -/
theorem mem_ker_etaCohomologyMap_iff (j : ℤ) (ξ : Hcohom C j) :
    ξ ∈ LinearMap.ker (etaCohomologyMap C j) ↔ f • ξ = 0 :=
  LinearMap.mem_ker.trans (etaCohomologyMap_eq_zero_iff C j ξ)

/-- The kernel of multiplication by `f^{j+1}` is the `f`-torsion submodule
`H^{j+1}(M^•)[f] = ker (ξ ↦ f • ξ)`. -/
theorem ker_etaCohomologyMap (j : ℤ) :
    LinearMap.ker (etaCohomologyMap C j) =
      LinearMap.ker (f • LinearMap.id (R := A) (M := Hcohom C j)) := by
  ext ξ
  rw [mem_ker_etaCohomologyMap_iff, LinearMap.mem_ker, LinearMap.smul_apply,
    LinearMap.id_apply]

/-- The map `H^{j+1}(M^•) / H^{j+1}(M^•)[f] → H^{j+1}(η_f M^•)` induced by multiplication by
`f^{j+1}`, i.e. by `etaCohomologyMap`, which kills the `f`-torsion
`H^{j+1}(M^•)[f] = ker (ξ ↦ f • ξ)`. -/
noncomputable def etaCohomologyTorsionMap (j : ℤ) :
    (Hcohom C j ⧸ LinearMap.ker (f • LinearMap.id (R := A) (M := Hcohom C j))) →ₗ[A]
      Heta C j :=
  (LinearMap.ker (f • LinearMap.id (R := A) (M := Hcohom C j))).liftQ (etaCohomologyMap C j)
    (ker_etaCohomologyMap C j).ge

/-- **The canonical isomorphism of Tag 0F7P.** For a complex `M^•` of `f`-torsion free
`A`-modules, the map `H^{j+1}(M^•) / H^{j+1}(M^•)[f] → H^{j+1}(η_f M^•)` (with
`H^{j+1}(M^•)[f] = ker (ξ ↦ f • ξ)` the `f`-torsion) sending the class of a
cocycle `z` to the class of `f^{j+1} z` is bijective, i.e. an isomorphism of `A`-modules.  The
source's index `i` is `j + 1` here, and every `i ∈ ℤ` arises. -/
@[stacks 0F7P "the map H^i(M)/H^i(M)[f] → H^i(η_f M), [z] ↦ [f^i z], is bijective, for every \
complex of f-torsion free modules; i = j + 1, and f need not be a nonzerodivisor on A"]
theorem bijective_etaCohomologyTorsionMap (j : ℤ) :
    Function.Bijective (etaCohomologyTorsionMap C j) ∧
      ∀ z : Zc C j,
        etaCohomologyTorsionMap C j (Submodule.Quotient.mk (Submodule.Quotient.mk z)) =
          Submodule.Quotient.mk (⟨fpowZ C j z, fpowZ_mem_Zeta C j z⟩ : Zeta C j) := by
  refine ⟨⟨?_, ?_⟩, fun z => rfl⟩
  · rw [← LinearMap.ker_eq_bot, etaCohomologyTorsionMap, Submodule.ker_liftQ,
      ker_etaCohomologyMap, Submodule.mkQ_map_self]
  · rw [← LinearMap.range_eq_top, etaCohomologyTorsionMap, Submodule.range_liftQ,
      LinearMap.range_eq_top]
    exact etaCohomologyMap_surjective C j

end Complex

/-! ## Main Statement (Stacks Tag 0F7P) -/

/-- Multiplication by `f^{j+1}` induces a surjective `A`-linear map
`Φ : H^{j+1}(M^•) → H^{j+1}(η_f M^•)` whose kernel is the `f`-torsion.

This is the surjective form; the canonical isomorphism out of the quotient is
`tag_0F7P_iso`. -/
theorem tag_0F7P (C : FTFComplex A f) (j : ℤ) :
    ∃ Φ : Hcohom C j →ₗ[A] Heta C j,
      Function.Surjective Φ ∧
      (∀ z : Zc C j, ∃ hz : fpowZ C j z ∈ Zeta C j,
        Φ (Submodule.Quotient.mk z) =
          Submodule.Quotient.mk (⟨fpowZ C j z, hz⟩ : Zeta C j)) ∧
      (∀ ξ : Hcohom C j, Φ ξ = 0 ↔ f • ξ = 0) :=
  ⟨etaCohomologyMap C j, etaCohomologyMap_surjective C j,
    fun z => ⟨fpowZ_mem_Zeta C j z, etaCohomologyMap_mk C j z⟩, etaCohomologyMap_eq_zero_iff C j⟩

/-- Existential packaging of `etaCohomologyMap` and `etaCohomologyEquiv`: some linear map
`Φ` with kernel the `f`-torsion, and an isomorphism out of `H^{j+1}(M^•) / ker Φ` through
which `Φ` factors.  The Stacks statement, with the canonical map named, is
`bijective_etaCohomologyTorsionMap`. -/
theorem tag_0F7P_iso (C : FTFComplex A f) (j : ℤ) :
    ∃ (Φ : Hcohom C j →ₗ[A] Heta C j)
      (e : (Hcohom C j ⧸ LinearMap.ker Φ) ≃ₗ[A] Heta C j),
      (∀ ξ : Hcohom C j, ξ ∈ LinearMap.ker Φ ↔ f • ξ = 0) ∧
      (∀ ξ : Hcohom C j, e (Submodule.Quotient.mk ξ) = Φ ξ) :=
  ⟨etaCohomologyMap C j, etaCohomologyEquiv C j, mem_ker_etaCohomologyMap_iff C j,
    etaCohomologyEquiv_mk C j⟩

@[deprecated (since := "2026-09-27")]
alias cocycles := Zc

@[deprecated (since := "2026-09-27")]
alias coboundaries := Bc

@[deprecated (since := "2026-09-27")]
alias CohomologyModule := Hcohom

@[deprecated (since := "2026-09-27")]
alias etaCocycles := Zeta

@[deprecated (since := "2026-09-27")]
alias etaCoboundaries := Beta

@[deprecated (since := "2026-09-27")]
alias EtaCohomology := Heta

@[deprecated (since := "2026-09-27")]
alias fpowCocycles := fpowZ

@[deprecated (since := "2026-09-27")]
alias fpowCocycles_apply := fpowZ_apply

@[deprecated (since := "2026-09-27")]
alias fpowCocycles_mem_etaCocycles := fpowZ_mem_Zeta

@[deprecated (since := "2026-09-27")]
alias fpow_coboundary_mem_etaCoboundaries := fpow_coboundary_mem_Beta

@[deprecated (since := "2026-09-27")]
alias fpowCocycles_mem_etaCoboundaries_iff := fpowZ_mem_Beta_iff

@[deprecated (since := "2026-09-27")]
alias exists_fpowCocycles_eq := exists_fpowZ_eq

end Stacks.Decalage.Cohomology
