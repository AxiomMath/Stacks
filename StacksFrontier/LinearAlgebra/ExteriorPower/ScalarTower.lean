module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exterior powers see only the ring that acts

Let `R → S` be a surjective ring map and let `M` be an `S`-module, viewed as an `R`-module
through `R → S`. The wedge of a family of elements of `M` may then be formed over `R` or over
`S`, and the universal property of the exterior power produces a comparison map

`⋀ⁿ_R(M) → ⋀ⁿ_S(M)`

carrying `m₁ ∧ ⋯ ∧ mₙ` to `m₁ ∧ ⋯ ∧ mₙ`. This file shows that the comparison is an isomorphism
for `n ≥ 1`: a scalar of `R` acts on `M` only through its image in `S`, so the `R`-alternating
maps out of `Mⁿ` and the `S`-alternating ones are the same maps, and the two exterior powers
have the same universal property.

The typical instance is `S = R ⧸ I` for an ideal `I` annihilating `M`, which is
`exteriorPower.quotientEquiv`.

## Main definitions

* `exteriorPower.towerMap`: the comparison map `⋀ⁿ_R(M) → ⋀ⁿ_S(M)`, defined for any scalar
  tower `R → S → M` with no surjectivity hypothesis.
* `exteriorPower.towerEquiv`: **the comparison is an isomorphism** `⋀ⁿ_R(M) ≃ₗ[R] ⋀ⁿ_S(M)` when
  `R → S` is surjective and `n ≥ 1`.
* `exteriorPower.quotientEquiv`: the same statement for `S = R ⧸ I`.

## Main results

* `exteriorPower.towerMap_ιMulti`: the comparison carries `m₁ ∧ ⋯ ∧ mₙ` formed over `R` to
  `m₁ ∧ ⋯ ∧ mₙ` formed over `S`. Since those wedges span, this pins the comparison down.
* `exteriorPower.towerMap_surjective`: surjectivity, in every degree.
* `exteriorPower.towerMap_injective`: injectivity in degrees `n ≥ 1`.
* `exteriorPower.zeroEquiv_towerMap`: in degree `0` the comparison *is* the ring map `R → S`
  read through `⋀⁰_R(M) ≃ R` and `⋀⁰_S(M) ≃ S`. This is why `n ≥ 1` is assumed above: the
  degree-`0` comparison is injective only when `R → S` is, so the isomorphism genuinely fails
  in degree `0` for every proper quotient.

## Implementation notes

The hypothesis "`M` is killed by `I`" is taken in the form `[Module S M]` together with
`[IsScalarTower R S M]` for an `R`-algebra `S` whose structure map is surjective, rather than
as an equation `I • M = 0` for an `R`-module `M`. Three reasons. The statement
`⋀ⁿ_R(M) ≃ ⋀ⁿ_{R/I}(M)` does not typecheck without an `R ⧸ I`-module structure on `M`, so an
equational hypothesis would force the statement to name a *constructed* instance; the present
form covers every surjective ring map, not only the quotient maps; and it is the form the
surrounding material on exterior powers over a ring map uses. An `R`-module `M` with
`I • M = 0` is brought into this form by `Module.IsTorsionBySet.module`.

**Where the mathematics happens.** Both directions are one application of the universal
property `exteriorPower.alternatingMapLinearEquiv`, and the work is in making each side's
alternating map available over the *other* ring.

Forwards this is free: an `S`-alternating map is in particular `R`-alternating, so
`exteriorPower.ιMulti S n` restricts to `R` and induces `towerMap`.

Backwards one must put an `S`-module structure on `⋀ⁿ_R(M)`, and that is exactly where `n ≥ 1`
enters: a scalar `r` in the kernel of `R → S` annihilates `⋀ⁿ_R(M)` for `n ≥ 1`, because it may
be moved onto the first slot of a wedge, where it already annihilates `M`
(`smul_eq_zero_of_algebraMap_eq_zero`); so `r • x` depends only on the image of `r`, and
`Function.Surjective.moduleLeft` turns the `R`-action into an `S`-action. For `n = 0` there is
no slot to move the scalar onto and the conclusion is false. With the `S`-action in hand
`exteriorPower.ιMulti R n` is `S`-alternating, and the map it induces on `⋀ⁿ_S(M)` is a
retraction of `towerMap`.

Surjectivity needs no degree hypothesis: the wedges span `⋀ⁿ_S(M)` over `S`, hence already
over `R` because `R → S` is surjective (`Submodule.restrictScalars_span`), and they are in the
image.
-/

@[expose] public section

namespace exteriorPower

section Tower

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (n : ℕ)

/-- The canonical alternating map `v ↦ v 0 ∧ ⋯ ∧ v (n-1)` into the exterior power over `S`,
read as an `R`-alternating map: an `S`-multilinear map is `R`-multilinear through `R → S`. -/
noncomputable def ιMultiRestrictScalars : M [⋀^Fin n]→ₗ[R] ⋀[S]^n M where
  toMultilinearMap := (ιMulti S n).toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' v _ _ h hij := (ιMulti S n).map_eq_zero_of_eq v h hij

/-- Restricting the scalars does not change the underlying function. -/
@[simp]
theorem ιMultiRestrictScalars_apply (v : Fin n → M) :
    ιMultiRestrictScalars R S M n v = ιMulti S n v :=
  rfl

/-- The comparison map `⋀ⁿ_R(M) → ⋀ⁿ_S(M)` between the exterior powers of `M` over the two
rings of the tower, induced by the universal property over `R` from the wedge over `S`. -/
noncomputable def towerMap : ⋀[R]^n M →ₗ[R] ⋀[S]^n M :=
  alternatingMapLinearEquiv (ιMultiRestrictScalars R S M n)

/-- The comparison map carries the wedge `v 0 ∧ ⋯ ∧ v (n-1)` formed over `R` to the wedge of
the same family formed over `S`. -/
@[simp]
theorem towerMap_ιMulti (v : Fin n → M) : towerMap R S M n (ιMulti R n v) = ιMulti S n v :=
  alternatingMapLinearEquiv_apply_ιMulti _ v

/-- The comparison map is surjective in every degree: the wedges span the exterior power over
`S`, hence also over `R` since `R → S` is surjective, and they are in the image. -/
theorem towerMap_surjective (hsurj : Function.Surjective (algebraMap R S)) :
    Function.Surjective (towerMap R S M n) := by
  have hspan : Submodule.span R (Set.range (ιMulti S n (M := M))) =
      (⊤ : Submodule R (⋀[S]^n M)) := by
    rw [← Submodule.restrictScalars_span R S hsurj, ιMulti_span S n M,
      Submodule.restrictScalars_top]
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  rintro x ⟨v, rfl⟩
  exact ⟨ιMulti R n v, towerMap_ιMulti R S M n v⟩

/-- In degree `0` the comparison map is the ring map `R → S` itself, read through the canonical
identifications `⋀⁰_R(M) ≃ R` and `⋀⁰_S(M) ≃ S`. -/
theorem zeroEquiv_towerMap (x : ⋀[R]^0 M) :
    zeroEquiv S M (towerMap R S M 0 x) = algebraMap R S (zeroEquiv R M x) := by
  obtain ⟨c, rfl⟩ := (zeroEquiv R M).symm.surjective x
  have h1 : (zeroEquiv R M).symm 1 = ιMulti R 0 (fun i : Fin 0 => i.elim0) :=
    (LinearEquiv.symm_apply_eq _).2 (zeroEquiv_ιMulti _).symm
  have hx : (zeroEquiv R M).symm c = c • ιMulti R 0 (fun i : Fin 0 => i.elim0) := by
    rw [← h1, ← map_smul, smul_eq_mul, mul_one]
  rw [LinearEquiv.apply_symm_apply, hx, map_smul, towerMap_ιMulti, ← algebraMap_smul S c,
    map_smul, zeroEquiv_ιMulti, smul_eq_mul, mul_one]

variable {R S M n}

/-- A scalar of `R` that dies in `S` annihilates `⋀ⁿ_R(M)` for `n ≥ 1`: moved onto the first
slot of a wedge it already annihilates `M`. -/
theorem smul_eq_zero_of_algebraMap_eq_zero (hn : 0 < n) {r : R}
    (hr : algebraMap R S r = 0) (x : ⋀[R]^n M) : r • x = 0 := by
  have key : (r • LinearMap.id : ⋀[R]^n M →ₗ[R] ⋀[R]^n M) = 0 := by
    refine linearMap_ext (AlternatingMap.ext fun v => ?_)
    have hv : r • v ⟨0, hn⟩ = (0 : M) := by
      rw [← algebraMap_smul S r (v ⟨0, hn⟩), hr, zero_smul]
    have hmove : ιMulti R n (Function.update v ⟨0, hn⟩ (r • v ⟨0, hn⟩)) = r • ιMulti R n v := by
      rw [AlternatingMap.map_update_smul, Function.update_eq_self]
    change r • ιMulti R n v = 0
    rw [← hmove, hv, AlternatingMap.map_update_zero]
  simpa using LinearMap.congr_fun key x

/-- For `n ≥ 1` the action of a scalar of `R` on `⋀ⁿ_R(M)` depends only on its image in `S`. -/
theorem smul_eq_smul_of_algebraMap_eq (hn : 0 < n) {r r' : R}
    (h : algebraMap R S r = algebraMap R S r') (x : ⋀[R]^n M) : r • x = r' • x := by
  rw [← sub_eq_zero, ← sub_smul]
  exact smul_eq_zero_of_algebraMap_eq_zero (S := S) hn (by rw [map_sub, h, sub_self]) x

/-- The comparison map is injective in degrees `n ≥ 1`. The `S`-action on `⋀ⁿ_R(M)` obtained
from `smul_eq_smul_of_algebraMap_eq` makes the wedge over `R` an `S`-alternating map, and the
map it induces on `⋀ⁿ_S(M)` is a retraction. -/
theorem towerMap_injective (hsurj : Function.Surjective (algebraMap R S)) (hn : 0 < n) :
    Function.Injective (towerMap R S M n) := by
  let _ : SMul S (⋀[R]^n M) := ⟨fun s x => Function.surjInv hsurj s • x⟩
  have hsmul : ∀ (c : R) (x : ⋀[R]^n M), algebraMap R S c • x = c • x := fun c x =>
    smul_eq_smul_of_algebraMap_eq (S := S) hn (Function.surjInv_eq hsurj _) x
  let _ : Module S (⋀[R]^n M) := hsurj.moduleLeft (algebraMap R S) hsmul
  have hsmul' : ∀ (s : S) (x : ⋀[R]^n M), s • x = Function.surjInv hsurj s • x :=
    fun _ _ => rfl
  let _ : IsScalarTower R S (⋀[R]^n M) := by
    refine ⟨fun r s x => ?_⟩
    have h1 : r • s = algebraMap R S (r * Function.surjInv hsurj s) := by
      rw [map_mul, Function.surjInv_eq hsurj s, Algebra.smul_def]
    rw [h1, hsmul, mul_smul, hsmul' s x]
  let alt : M [⋀^Fin n]→ₗ[S] ⋀[R]^n M :=
    { toFun := ιMulti R n
      map_update_add' m i x y := (ιMulti R n).map_update_add m i x y
      map_update_smul' m i s x := by
        obtain ⟨r, rfl⟩ := hsurj s
        rw [algebraMap_smul, algebraMap_smul, AlternatingMap.map_update_smul]
      map_eq_zero_of_eq' v _ _ h hij := (ιMulti R n).map_eq_zero_of_eq v h hij }
  have key : (alternatingMapLinearEquiv alt).restrictScalars R ∘ₗ towerMap R S M n =
      LinearMap.id := by
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, towerMap_ιMulti, alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.id_coe, id_eq]
    rfl
  exact Function.LeftInverse.injective (g := alternatingMapLinearEquiv alt)
    (LinearMap.congr_fun key)

variable (R S M n)

/-- **The exterior power only depends on the ring that acts.** If `R → S` is surjective and `M`
is an `S`-module, then for `n ≥ 1` the comparison map is an isomorphism
`⋀ⁿ_R(M) ≃ₗ[R] ⋀ⁿ_S(M)`. -/
noncomputable def towerEquiv (hsurj : Function.Surjective (algebraMap R S)) (hn : 0 < n) :
    ⋀[R]^n M ≃ₗ[R] ⋀[S]^n M :=
  LinearEquiv.ofBijective (towerMap R S M n)
    ⟨towerMap_injective hsurj hn, towerMap_surjective R S M n hsurj⟩

/-- The isomorphism carries the wedge `v 0 ∧ ⋯ ∧ v (n-1)` formed over `R` to the wedge of the
same family formed over `S`. -/
@[simp]
theorem towerEquiv_ιMulti (hsurj : Function.Surjective (algebraMap R S)) (hn : 0 < n)
    (v : Fin n → M) : towerEquiv R S M n hsurj hn (ιMulti R n v) = ιMulti S n v :=
  towerMap_ιMulti R S M n v

/-- The inverse isomorphism carries the wedge formed over `S` to the wedge formed over `R`. -/
@[simp]
theorem towerEquiv_symm_ιMulti (hsurj : Function.Surjective (algebraMap R S)) (hn : 0 < n)
    (v : Fin n → M) : (towerEquiv R S M n hsurj hn).symm (ιMulti S n v) = ιMulti R n v :=
  (LinearEquiv.symm_apply_eq _).2 (towerEquiv_ιMulti R S M n hsurj hn v).symm

end Tower

section Quotient

variable (R : Type*) [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
  [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] (n : ℕ)

/-- **The exterior power of a module killed by an ideal.** Let `I` be an ideal of `R` and let
`M` be an `R`-module on which `R` acts through `R ⧸ I`. Then for `n ≥ 1` the canonical map is
an isomorphism `⋀ⁿ_R(M) ≃ₗ[R] ⋀ⁿ_{R/I}(M)`. -/
noncomputable def quotientEquiv (hn : 0 < n) : ⋀[R]^n M ≃ₗ[R] ⋀[R ⧸ I]^n M :=
  towerEquiv R (R ⧸ I) M n Ideal.Quotient.mk_surjective hn

/-- The isomorphism carries the wedge `v 0 ∧ ⋯ ∧ v (n-1)` formed over `R` to the wedge of the
same family formed over `R ⧸ I`. -/
@[simp]
theorem quotientEquiv_ιMulti (hn : 0 < n) (v : Fin n → M) :
    quotientEquiv R I M n hn (ιMulti R n v) = ιMulti (R ⧸ I) n v :=
  towerMap_ιMulti R (R ⧸ I) M n v

/-- The inverse isomorphism carries the wedge formed over `R ⧸ I` to the wedge formed
over `R`. -/
@[simp]
theorem quotientEquiv_symm_ιMulti (hn : 0 < n) (v : Fin n → M) :
    (quotientEquiv R I M n hn).symm (ιMulti (R ⧸ I) n v) = ιMulti R n v :=
  (LinearEquiv.symm_apply_eq _).2 (quotientEquiv_ιMulti R I M n hn v).symm

end Quotient

end exteriorPower
