module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Divided power differential forms of a quotient, and the second equality of [Stacks, Tag 07LF]

Let `δ` be divided powers on an ideal `J` of a `A`-algebra `B`, let `K ⊆ J` be a
sub-divided-power ideal all of whose universal differentials lie in `K · Ω_{B/A,δ}`, and let
`δ̄` be the induced divided powers on `B ⧸ K`.  This module proves that

`Ω^i_{(B ⧸ K)/A, δ̄} = (B ⧸ K) ⊗_B Ω^i_{B/A, δ}`

in every degree `i`, and deduces the equality the source's proof of [Stacks, Tag 07LF] calls
its *second* equality: for every `B ⧸ K`-module `M`,

`M ⊗_{B ⧸ K} Ω^i_{(B ⧸ K)/A, δ̄} = M ⊗_B Ω^i_{B/A, δ}`.

The crystalline situation this is used in is `B = D(n)`, the `p`-adically completed divided
power envelope of [Stacks, Tag 07J8], `K = (p)^{N + e}`, so that `B ⧸ K = D(n)/(p)^{N + e}` is
the ring of sections of the level `(n, e)` of the system of [Stacks, Tag 07JN], and
`M = Γ((X, T(n)_e, δ(n)), F)`.  Nothing here mentions the crystalline site: the statement is
one about a divided power ring and a sub-divided-power ideal, and the hypothesis `hd` on the
universal differentials is discharged at `K = (p)^n` by
`Crystalline.dividedPowerDifferential_mem_pAdicPow`.

## The two halves

The degree-one half is `Crystalline.differentialsQuotientEquiv` of
`ModuleDifferentials/Functoriality.lean`, which says that `Ω_{(B ⧸ K)/A, δ̄}` is
`Ω_{B/A, δ} ⧸ K · Ω_{B/A, δ}`; `isBaseChange_of_quotientLinearEquiv` reads such a quotient
description as the statement that the reduction map is a base change.  The passage from degree
one to degree `i` is `ExteriorAlgebra.exteriorPowerBaseChange`, and the cancellation of the two
tensor products is `TensorProduct.AlgebraTensorModule.cancelBaseChange`.

No flatness, no finiteness and no hypothesis on `i` appears.  In particular the route does not
go through `exteriorPower.towerEquiv` of
`StacksFrontier/LinearAlgebra/ExteriorPower/ScalarTower.lean`, which compares `⋀^i_B` with
`⋀^i_{B ⧸ K}` on one and the same module and is false in degree zero; here the module itself is
base changed, and degree zero is the harmless statement `M ⊗_{B ⧸ K} (B ⧸ K) = M ⊗_B B`.

## Main definitions

* `Crystalline.quotientDividedPowersOfSubDPIdeal` — the divided powers `δ̄` induced on `B ⧸ K`
  by a sub-divided-power ideal `K`, named so that the statements below can be made about it.
* `Crystalline.differentialsQuotientMap` — the reduction `Ω_{B/A, δ} ⟶ Ω_{(B ⧸ K)/A, δ̄}`, as a
  `B`-linear map.
* `Crystalline.differentialsQuotientBaseChangeEquiv` and
  `Crystalline.formsQuotientBaseChangeEquiv` — `(B ⧸ K) ⊗_B Ω^i_{B/A, δ} ≃ Ω^i_{(B ⧸ K)/A, δ̄}`,
  in degree one and in every degree.
* `Crystalline.tensorFormsQuotientEquiv` — **the second equality of the source's proof of
  [Stacks, Tag 07LF]**: `M ⊗_{B ⧸ K} Ω^i_{(B ⧸ K)/A, δ̄} ≃ M ⊗_B Ω^i_{B/A, δ}`.
* `Crystalline.formsQuotientMapₛₗ` — the degree-`i` reduction retyped as a semilinear map along
  `B ⟶ B ⧸ K`, which is the shape `Crystalline.mapDifferentialFormsOfDPMorphism_ext` compares.

## Main results

* `Crystalline.isBaseChange_of_quotientLinearEquiv` — a `B`-linear map whose source modulo
  `K · (source)` is its target is a base change along `B ⟶ B ⧸ K`.
* `Crystalline.isBaseChange_differentialsQuotientMap` and
  `Crystalline.isBaseChange_formsQuotientMap` — the reduction maps on `Ω` and on `Ω^i` are base
  changes.
* `Crystalline.formsQuotientBaseChangeEquiv_tmul_ιMulti`,
  `Crystalline.tensorFormsQuotientEquiv_symm_tmul` and
  `Crystalline.tensorFormsQuotientEquiv_tmul_ιMulti` — the equivalences on the standard
  generators, which is what identifies them as the canonical maps rather than merely as some
  bijections.

### The reduction is the functorial map, and the second equality is natural

* `Crystalline.isDPMorphism_quotientMkₐ` — the quotient map `B ⟶ B ⧸ K` is a divided power
  morphism onto `δ̄`.
* `Crystalline.differentialsQuotientMap_eq` and `Crystalline.formsQuotientMap_eq` — **the
  reductions are the functorial maps `Crystalline.mapDifferentialsOfDPMorphism` and
  `Crystalline.mapDifferentialFormsOfDPMorphism` of that divided power morphism**, in degree one
  and in every degree.  Nothing new is proved by either; they are what turns a naturality square
  into two applications of the composition law for the functorial maps.
* `Crystalline.isDPMorphism_quotientComp` and `Crystalline.isDPMorphism_quotientMapₐ` — a
  divided power morphism `f : (B, J, δ) ⟶ (C, L, ε)` over `A` carrying `K` into `K'` descends to
  a divided power morphism `f̄ : B ⧸ K ⟶ C ⧸ K'` of the induced divided powers.
* `Crystalline.differentialsQuotientMap_naturality` and
  `Crystalline.formsQuotientMap_naturality` — **the reduction is natural in the divided power
  ring**: reducing and transporting along `f̄` is transporting along `f` and reducing, in degree
  one and in every degree.
* `Crystalline.tensorFormsQuotientEquiv_symm_naturality` and its `p`-adic-level form
  `Crystalline.tensorFormsLevelEquiv_symm_naturality` — **the second equality is natural in the
  divided power ring.**  This is the cosimplicial-direction naturality the source's proof of
  [Stacks, Tag 07LF] asks of its second equality: `f` is the transition map `D(n) ⟶ D(m)` of the
  cosimplicial envelope, `K` and `K'` are `(p)^{N + e}` on the two sides, and `f̄` is the
  transition map of the level rings.
* `Crystalline.pAdicIdeal_pow_le_comap_ringHom` — every ring homomorphism carries `(p)^k` into
  `(p)^k`, so the descent to the levels needs no hypothesis.

## What is and is not proved

Everything here is proved, with no hypothesis beyond `hK` and `hd`, which the degree-one
statement `Crystalline.differentialsQuotientEquiv` already carries.  **No tag attribute is
placed**: this is one of the two equalities inside the source's proof of [Stacks, Tag 07LF],
not a clause of that tag's statement, and the other input of that proof — the assembly of
`n ↦ M(n)_e` into a cosimplicial module over `D(*)` — is not proved here.

The naturality statements are **elementwise**, on a section of `M` and a form over `B`, and not
equalities of two maps `M ⊗_B Ω^i_{B/A,δ} ⟶ M ⊗_{C ⧸ K'} Ω^i_{(C ⧸ K')/A,ε̄}`.  The two vertical
maps of the square are semilinear over different base rings in source and target, and the
library has no tensor product of semilinear maps across a square of rings to name them with.
Nothing is lost: the transport of the first factor is the identity on `m` on both sides, pure
tensors span, and `m` is arbitrary.

The isomorphism `ε` of [Stacks, Tag 07LF] needs the cosimplicial naturality of both
comparisons.  Only the second is proved here; the naturality of
`Crystalline.tensorFormsCompletionLevelEquiv` of `ModuleDifferentials/CompletionLevelForms.lean`
— the comparison of the two shapes of `Ω_{D(n)}` — is
`Crystalline.tensorFormsCompletionLevelEquivAt_naturality` of
`ModuleDifferentials/CompletionLevelFormsNaturality.lean`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
-/

@[expose] public section

open scoped TensorProduct

universe u v

noncomputable section

namespace Crystalline

/-! ### A quotient description of a linear map makes it a base change -/

section QuotientBaseChange

variable {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
  [IsScalarTower R S Y]

/-- **A `R`-linear map `f : X ⟶ Y` into an `S`-module which exhibits `Y` as `X ⧸ K · X`, for `K`
the kernel of `R ⟶ S`, is a base change along `R ⟶ S`.**

Both directions of the universal property are read off the lift of `f` to the quotient: a map
out of `X` killing `K · X` factors through `X ⧸ K · X`, hence through `Y`, and two `S`-linear
maps out of `Y` agreeing after `f` agree on the image of the quotient map, which is all of
`Y`. -/
theorem isBaseChange_of_quotientLinearEquiv (f : X →ₗ[R] Y)
    (hs : Function.Surjective (algebraMap R S))
    (K : Ideal R) (hK : K = RingHom.ker (algebraMap R S))
    (E : (X ⧸ K • (⊤ : Submodule R X)) ≃ₗ[R] Y)
    (hE : ∀ x, E (Submodule.Quotient.mk x) = f x) :
    IsBaseChange S f := by
  apply IsBaseChange.of_lift_unique _
  intro Q _ _ _ _ g
  let _ := Module.addCommMonoidToAddCommGroup S (M := Q)
  have hg : K • (⊤ : Submodule R X) ≤ g.ker := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ g.ker.add_mem hx hy)
    change g (r • x) = 0
    have hr' : algebraMap R S r = 0 := RingHom.mem_ker.mp (hK ▸ hr)
    rw [map_smul, ← IsScalarTower.algebraMap_smul S, hr', zero_smul]
  let L := (K • (⊤ : Submodule R X)).liftQ g hg
  refine ⟨LinearMap.extendScalarsOfSurjective hs (L.comp E.symm.toLinearMap), ?_, ?_⟩
  · ext x
    change L (E.symm (f x)) = g x
    rw [← hE, E.symm_apply_apply]
    rfl
  · intro F hF
    ext y
    obtain ⟨z, rfl⟩ := E.surjective y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    change F (E (Submodule.Quotient.mk x)) = L (E.symm (E (Submodule.Quotient.mk x)))
    rw [E.symm_apply_apply, hE]
    exact LinearMap.congr_fun hF x

end QuotientBaseChange

/-! ### The divided power differentials of a quotient as a base change -/

section QuotientForms

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (J : Ideal B) (delta : DividedPowers J) (K : Ideal B)

/-- **The divided powers `δ̄` induced on `B ⧸ K` by a sub-divided-power ideal `K`.**  This is
`DividedPowers.Quotient.dividedPowers` with the hypothesis in the form
`DividedPowers.IsSubDPIdeal delta K`, which is the form `Crystalline.differentialsQuotientEquiv`
takes it in. -/
abbrev quotientDividedPowersOfSubDPIdeal (hK : delta.IsSubDPIdeal K) :
    DividedPowers (J.map (Ideal.Quotient.mk K)) :=
  DividedPowers.Quotient.dividedPowers delta
    (by simpa [inf_of_le_left hK.isSubideal] using hK)

variable (hK : delta.IsSubDPIdeal K)
  (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
    K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta)))

include hK hd

/-- **The reduction `Ω_{B/A, δ} ⟶ Ω_{(B ⧸ K)/A, δ̄}`**, as a `B`-linear map: the quotient map by
`K · Ω_{B/A, δ}` followed by the identification of `Crystalline.differentialsQuotientEquiv`. -/
def differentialsQuotientMap :
    dividedPowerDifferentials (A := A) delta →ₗ[B]
      dividedPowerDifferentials (A := A) (quotientDividedPowersOfSubDPIdeal J delta K hK) :=
  (differentialsQuotientEquiv (A := A) J delta K hK hd).val.toLinearMap ∘ₗ
    (K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))).mkQ

/-- **The reduction carries universal differentials to universal differentials.** -/
theorem differentialsQuotientMap_d (b : B) :
    differentialsQuotientMap J delta K hK hd (dividedPowerDifferential (A := A) delta b) =
      dividedPowerDifferential (A := A) (quotientDividedPowersOfSubDPIdeal J delta K hK)
        (Ideal.Quotient.mk K b) :=
  (differentialsQuotientEquiv (A := A) J delta K hK hd).property b

/-- **`Ω_{(B ⧸ K)/A, δ̄}` is the base change of `Ω_{B/A, δ}` along `B ⟶ B ⧸ K`.** -/
theorem isBaseChange_differentialsQuotientMap :
    IsBaseChange (B ⧸ K) (differentialsQuotientMap J delta K hK hd) := by
  refine isBaseChange_of_quotientLinearEquiv _ ?_ K ?_
    (differentialsQuotientEquiv (A := A) J delta K hK hd).val (fun _ ↦ rfl)
  · rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- **`Ω_{(B ⧸ K)/A, δ̄} = (B ⧸ K) ⊗_B Ω_{B/A, δ}`**, in degree one. -/
def differentialsQuotientBaseChangeEquiv :
    (B ⧸ K) ⊗[B] dividedPowerDifferentials (A := A) delta ≃ₗ[B ⧸ K]
      dividedPowerDifferentials (A := A) (quotientDividedPowersOfSubDPIdeal J delta K hK) :=
  (isBaseChange_differentialsQuotientMap J delta K hK hd).equiv

/-- The degree-one identification carries `a ⊗ x` to `a` times the reduction of `x`. -/
@[simp]
theorem differentialsQuotientBaseChangeEquiv_tmul (a : B ⧸ K)
    (x : dividedPowerDifferentials (A := A) delta) :
    differentialsQuotientBaseChangeEquiv J delta K hK hd (a ⊗ₜ x) =
      a • differentialsQuotientMap J delta K hK hd x :=
  IsBaseChange.equiv_tmul _ a x

/-- **The reduction `Ω^i_{B/A, δ} ⟶ Ω^i_{(B ⧸ K)/A, δ̄}` in degree `i`**, the `i`-th exterior
power of `Crystalline.differentialsQuotientMap` taken along the ring map `B ⟶ B ⧸ K`. -/
def formsQuotientMap (i : ℕ) :
    dividedPowerDifferentialForms (A := A) delta i →ₗ[B]
      dividedPowerDifferentialForms (A := A)
        (quotientDividedPowersOfSubDPIdeal J delta K hK) i :=
  (LinearMap.restrictScalars B
      (exteriorPower.map i
        (differentialsQuotientBaseChangeEquiv J delta K hK hd).toLinearMap)).comp
    (ExteriorAlgebra.exteriorPowerBaseChangeMap B (B ⧸ K)
      (dividedPowerDifferentials (A := A) delta) i)

/-- The degree-`i` reduction carries a wedge of differentials to the wedge of their reductions. -/
theorem formsQuotientMap_ιMulti (i : ℕ)
    (v : Fin i → dividedPowerDifferentials (A := A) delta) :
    formsQuotientMap J delta K hK hd i (exteriorPower.ιMulti B i v) =
      exteriorPower.ιMulti (B ⧸ K) i
        (fun j ↦ differentialsQuotientMap J delta K hK hd (v j)) := by
  have hv : ((differentialsQuotientBaseChangeEquiv J delta K hK hd).toLinearMap ∘
        fun j ↦ (1 : B ⧸ K) ⊗ₜ[B] v j) =
      fun j ↦ differentialsQuotientMap J delta K hK hd (v j) := by
    funext j
    change differentialsQuotientBaseChangeEquiv J delta K hK hd ((1 : B ⧸ K) ⊗ₜ[B] v j) = _
    rw [differentialsQuotientBaseChangeEquiv_tmul, one_smul]
  change exteriorPower.map i (differentialsQuotientBaseChangeEquiv J delta K hK hd).toLinearMap
      (ExteriorAlgebra.exteriorPowerBaseChangeMap B (B ⧸ K)
        (dividedPowerDifferentials (A := A) delta) i (exteriorPower.ιMulti B i v)) = _
  rw [ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti, exteriorPower.map_apply_ιMulti, hv]

/-- **`Ω^i_{(B ⧸ K)/A, δ̄}` is the base change of `Ω^i_{B/A, δ}` along `B ⟶ B ⧸ K`**, in every
degree. -/
theorem isBaseChange_formsQuotientMap (i : ℕ) :
    IsBaseChange (B ⧸ K) (formsQuotientMap J delta K hK hd i) :=
  DeRhamBaseChange.isBaseChange_exteriorPower
    (isBaseChange_differentialsQuotientMap J delta K hK hd) _
    (formsQuotientMap_ιMulti J delta K hK hd i)

/-- **The first half of the second equality of the source's proof of [Stacks, Tag 07LF]**:

`Ω^i_{(B ⧸ K)/A, δ̄} = (B ⧸ K) ⊗_B Ω^i_{B/A, δ}`

in every degree `i`. -/
def formsQuotientBaseChangeEquiv (i : ℕ) :
    (B ⧸ K) ⊗[B] dividedPowerDifferentialForms (A := A) delta i ≃ₗ[B ⧸ K]
      dividedPowerDifferentialForms (A := A)
        (quotientDividedPowersOfSubDPIdeal J delta K hK) i :=
  (isBaseChange_formsQuotientMap J delta K hK hd i).equiv

/-- The degree-`i` identification carries `a ⊗ x` to `a` times the reduction of `x`. -/
@[simp]
theorem formsQuotientBaseChangeEquiv_tmul (i : ℕ) (a : B ⧸ K)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    formsQuotientBaseChangeEquiv J delta K hK hd i (a ⊗ₜ x) =
      a • formsQuotientMap J delta K hK hd i x :=
  IsBaseChange.equiv_tmul _ a x

/-- The identification of the forms of degree `i` on the standard generators. -/
theorem formsQuotientBaseChangeEquiv_tmul_ιMulti (i : ℕ) (a : B ⧸ K)
    (v : Fin i → dividedPowerDifferentials (A := A) delta) :
    formsQuotientBaseChangeEquiv J delta K hK hd i (a ⊗ₜ exteriorPower.ιMulti B i v) =
      a • exteriorPower.ιMulti (B ⧸ K) i
        (fun j ↦ differentialsQuotientMap J delta K hK hd (v j)) := by
  rw [formsQuotientBaseChangeEquiv_tmul, formsQuotientMap_ιMulti]

/-! ### The second equality of the source's proof of [Stacks, Tag 07LF] -/

section Tensor

variable (M : Type*) [AddCommGroup M] [Module B M] [Module (B ⧸ K) M]
  [IsScalarTower B (B ⧸ K) M]

/-- **The second equality of the source's proof of [Stacks, Tag 07LF].**  For a module `M` over
the quotient `B ⧸ K`,

`M ⊗_{B ⧸ K} Ω^i_{(B ⧸ K)/A, δ̄} = M ⊗_B Ω^i_{B/A, δ}`.

In the situation of [Stacks, Tag 07LF] this is read at `B = D(n)`, `K = (p)^{N + e}` — so that
`B ⧸ K` is the ring of sections of the level `(n, e)` of the system of [Stacks, Tag 07JN] — and
`M = M(n)_e`, where it says that the uncompleted tensor product of `M(n)_e` with the forms of
the level is the uncompleted tensor product with the forms of `D(n)`, which is what lets the
source apply [Stacks, Tag 07LA] over `D(*)` to the level-`e` cosimplicial module.

It is `formsQuotientBaseChangeEquiv` — the forms of the quotient are the base change of the
forms — followed by `TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
def tensorFormsQuotientEquiv (i : ℕ) :
    M ⊗[B ⧸ K] dividedPowerDifferentialForms (A := A)
        (quotientDividedPowersOfSubDPIdeal J delta K hK) i ≃ₗ[B ⧸ K]
      M ⊗[B] dividedPowerDifferentialForms (A := A) delta i :=
  (TensorProduct.congr (LinearEquiv.refl (B ⧸ K) M)
      (formsQuotientBaseChangeEquiv J delta K hK hd i).symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ K) (B ⧸ K) M
      (dividedPowerDifferentialForms (A := A) delta i))

/-- The inverse of the second equality carries `m ⊗ x` to `m` tensored with the reduction of
`x`. -/
@[simp]
theorem tensorFormsQuotientEquiv_symm_tmul (i : ℕ) (m : M)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    (tensorFormsQuotientEquiv J delta K hK hd M i).symm (m ⊗ₜ x) =
      m ⊗ₜ formsQuotientMap J delta K hK hd i x := by
  rw [tensorFormsQuotientEquiv, LinearEquiv.symm_trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.congr_symm, LinearEquiv.refl_symm, LinearEquiv.symm_symm,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    formsQuotientBaseChangeEquiv_tmul, one_smul]

/-- **The second equality on the standard generators**: a tensor of a section with a wedge of
reduced universal differentials is the tensor of the section with the wedge of the universal
differentials themselves. -/
theorem tensorFormsQuotientEquiv_tmul_ιMulti (i : ℕ) (m : M)
    (v : Fin i → dividedPowerDifferentials (A := A) delta) :
    tensorFormsQuotientEquiv J delta K hK hd M i
        (m ⊗ₜ exteriorPower.ιMulti (B ⧸ K) i
          (fun j ↦ differentialsQuotientMap J delta K hK hd (v j))) =
      m ⊗ₜ exteriorPower.ιMulti B i v := by
  apply (tensorFormsQuotientEquiv J delta K hK hd M i).symm.injective
  rw [LinearEquiv.symm_apply_apply, tensorFormsQuotientEquiv_symm_tmul,
    formsQuotientMap_ιMulti]

end Tensor

end QuotientForms

/-! ### The reduction maps are the functorial maps of the quotient divided power morphism -/

section QuotientFunctorial

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (J : Ideal B) (delta : DividedPowers J) (K : Ideal B) (hK : delta.IsSubDPIdeal K)

/-- **The quotient map `B ⟶ B ⧸ K` is a divided power morphism** onto the divided powers `δ̄`
induced by a sub-divided-power ideal.  This is `DividedPowers.Quotient.isDPMorphism` with the
hypothesis in the form `Crystalline.quotientDividedPowersOfSubDPIdeal` takes it. -/
theorem isDPMorphism_quotientMkₐ :
    DividedPowers.IsDPMorphism delta (quotientDividedPowersOfSubDPIdeal J delta K hK)
      (Ideal.Quotient.mkₐ A K).toRingHom :=
  DividedPowers.Quotient.isDPMorphism delta
    (by simpa [inf_of_le_left hK.isSubideal] using hK)

variable (hd : ∀ b ∈ K, dividedPowerDifferential (A := A) delta b ∈
  K • (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta)))

include hK hd

/-- **The reduction `Ω_{B/A, δ} ⟶ Ω_{(B ⧸ K)/A, δ̄}` is the functorial map of the quotient
divided power morphism.**  Nothing new is proved: this is
`Crystalline.differentialsQuotientEquiv_mk` read through the definition of
`Crystalline.differentialsQuotientMap`.  It is recorded because it is what turns the naturality
of the reduction into two applications of
`Crystalline.mapDifferentialsOfDPMorphism_comp`. -/
theorem differentialsQuotientMap_eq (x : dividedPowerDifferentials (A := A) delta) :
    differentialsQuotientMap J delta K hK hd x =
      mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
        (quotientDividedPowersOfSubDPIdeal J delta K hK) (Ideal.Quotient.mkₐ A K)
        (isDPMorphism_quotientMkₐ J delta K hK) x :=
  differentialsQuotientEquiv_mk (A := A) J delta K hK hd x

/-- **The degree-`i` reduction, repackaged as a semilinear map along `B ⟶ B ⧸ K`.**
`Crystalline.formsQuotientMap` is stated `B`-linearly into a target whose `B`-module structure is
restriction of scalars along `B ⟶ B ⧸ K`; `Crystalline.mapDifferentialFormsOfDPMorphism_ext`
compares semilinear maps, so the two have to be given the same type before they can be compared,
and this is that retyping.  The underlying function is unchanged. -/
def formsQuotientMapₛₗ (i : ℕ) :
    dividedPowerDifferentialForms (A := A) delta i →ₛₗ[
        (Ideal.Quotient.mkₐ A K : B →ₐ[A] B ⧸ K).toRingHom]
      dividedPowerDifferentialForms (A := A)
        (quotientDividedPowersOfSubDPIdeal J delta K hK) i where
  toFun := formsQuotientMap J delta K hK hd i
  map_add' := map_add _
  map_smul' b x :=
    ((formsQuotientMap J delta K hK hd i).map_smul b x).trans
      (IsScalarTower.algebraMap_smul (B ⧸ K) b
        (formsQuotientMap J delta K hK hd i x)).symm

/-- **The degree-`i` reduction is the functorial map of the quotient divided power morphism.**
Both carry a wedge to the wedge of the reductions slot by slot, by
`Crystalline.formsQuotientMap_ιMulti` and
`Crystalline.mapDifferentialFormsOfDPMorphism_ιMulti`, and those wedges span. -/
theorem formsQuotientMap_eq (i : ℕ) (x : dividedPowerDifferentialForms (A := A) delta i) :
    formsQuotientMap J delta K hK hd i x =
      mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
        (quotientDividedPowersOfSubDPIdeal J delta K hK) (Ideal.Quotient.mkₐ A K)
        (isDPMorphism_quotientMkₐ J delta K hK) i x := by
  refine DFunLike.congr_fun (mapDifferentialFormsOfDPMorphism_ext (A := A) (J := J)
    (delta := delta) (quotientDividedPowersOfSubDPIdeal J delta K hK)
    (Ideal.Quotient.mkₐ A K) i
    (F := formsQuotientMapₛₗ J delta K hK hd i) fun omega ↦ ?_) x
  change formsQuotientMap J delta K hK hd i _ = _
  rw [formsQuotientMap_ιMulti, mapDifferentialFormsOfDPMorphism_ιMulti]
  exact congrArg _ (funext fun j ↦ differentialsQuotientMap_eq J delta K hK hd (omega j))

omit hd

/-! ### Naturality of the second equality along a divided power morphism -/

section Naturality

variable {C : Type*} [CommRing C] [Algebra A C]
  (L : Ideal C) (epsilon : DividedPowers L) (K' : Ideal C) (hK' : epsilon.IsSubDPIdeal K')
  (hd' : ∀ c ∈ K', dividedPowerDifferential (A := A) epsilon c ∈
    K' • (⊤ : Submodule C (dividedPowerDifferentials (A := A) epsilon)))
  (f : B →ₐ[A] C) (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)
  (hKK' : K ≤ K'.comap f.toRingHom)

include hf

omit hK in
/-- **`B ⟶ C ⧸ K'` is a divided power morphism**, being `f` followed by the quotient map. -/
theorem isDPMorphism_quotientComp :
    DividedPowers.IsDPMorphism delta (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
      ((Ideal.Quotient.mkₐ A K').toRingHom.comp f.toRingHom) :=
  DividedPowers.IsDPMorphism.comp (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
    (isDPMorphism_quotientMkₐ L epsilon K' hK') hf

/-- **The descent `B ⧸ K ⟶ C ⧸ K'` of a divided power morphism carrying `K` into `K'` is again a
divided power morphism.**  The quotient map `B ⟶ B ⧸ K` is a surjective divided power morphism
carrying `J` onto the divided power ideal of the quotient, so
`DividedPowers.IsDPMorphism.of_comp` reduces this to the composite `B ⟶ C ⧸ K'`, which is
`isDPMorphism_quotientComp`. -/
theorem isDPMorphism_quotientMapₐ :
    DividedPowers.IsDPMorphism (quotientDividedPowersOfSubDPIdeal J delta K hK)
      (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
      (Ideal.quotientMapₐ K' f hKK').toRingHom :=
  DividedPowers.IsDPMorphism.of_comp delta
    (quotientDividedPowersOfSubDPIdeal J delta K hK)
    (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
    (Ideal.Quotient.mkₐ A K).toRingHom (Ideal.quotientMapₐ K' f hKK').toRingHom
    rfl (isDPMorphism_quotientMkₐ J delta K hK)
    (isDPMorphism_quotientComp J delta L epsilon K' hK' f hf)

include hd hK' hd' hKK'

/-- **The degree-one reduction is natural in the divided power ring.**  For a divided power
morphism `f : (B, J, δ) ⟶ (C, L, ε)` over `A` carrying `K` into `K'`, reducing and then
transporting along the descent `f̄ : B ⧸ K ⟶ C ⧸ K'` is transporting along `f` and then
reducing.

Both composites are the functorial map of one and the same divided power morphism `B ⟶ C ⧸ K'`,
by `Crystalline.differentialsQuotientMap_eq` and
`Crystalline.mapDifferentialsOfDPMorphism_comp`; the two spellings of that morphism —
`f̄ ∘ (B ⟶ B ⧸ K)` and `(C ⟶ C ⧸ K') ∘ f` — are the same ring map on the nose. -/
theorem differentialsQuotientMap_naturality (x : dividedPowerDifferentials (A := A) delta) :
    mapDifferentialsOfDPMorphism (A := A) (J := J.map (Ideal.Quotient.mk K))
        (delta := quotientDividedPowersOfSubDPIdeal J delta K hK)
        (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
        (Ideal.quotientMapₐ K' f hKK')
        (isDPMorphism_quotientMapₐ J delta K hK L epsilon K' hK' f hf hKK')
        (differentialsQuotientMap J delta K hK hd x) =
      differentialsQuotientMap L epsilon K' hK' hd'
        (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta) epsilon f hf x) := by
  rw [differentialsQuotientMap_eq J delta K hK hd, differentialsQuotientMap_eq L epsilon K' hK' hd']
  exact (DFunLike.congr_fun (mapDifferentialsOfDPMorphism_comp (A := A) (J := J)
    (delta := delta) (quotientDividedPowersOfSubDPIdeal J delta K hK)
    (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
    (Ideal.Quotient.mkₐ A K) (Ideal.quotientMapₐ K' f hKK')
    (isDPMorphism_quotientMkₐ J delta K hK)
    (isDPMorphism_quotientMapₐ J delta K hK L epsilon K' hK' f hf hKK')) x).trans
    (DFunLike.congr_fun (mapDifferentialsOfDPMorphism_comp (A := A) (J := J)
    (delta := delta) epsilon (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
    f (Ideal.Quotient.mkₐ A K') hf (isDPMorphism_quotientMkₐ L epsilon K' hK')) x).symm

/-- **The degree-`i` reduction is natural in the divided power ring.**  This is
`Crystalline.differentialsQuotientMap_naturality` carried up the exterior powers: in every degree
`i`, reducing `Ωⁱ_{B/A,δ}` and transporting along the descent `f̄` agrees with transporting along
`f` and reducing `Ωⁱ_{C/A,ε}`.

This is the naturality the cosimplicial direction of the source's proof of [Stacks, Tag 07LF]
asks of `Crystalline.tensorFormsQuotientEquiv`: there `f` is the transition map
`D(n) ⟶ D(m)` of the cosimplicial envelope and `K`, `K'` are `(p)^{N + e}` on the two sides, so
the descent `f̄` is the transition map of the levels. -/
theorem formsQuotientMap_naturality (i : ℕ)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    mapDifferentialFormsOfDPMorphism (A := A) (J := J.map (Ideal.Quotient.mk K))
        (delta := quotientDividedPowersOfSubDPIdeal J delta K hK)
        (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
        (Ideal.quotientMapₐ K' f hKK')
        (isDPMorphism_quotientMapₐ J delta K hK L epsilon K' hK' f hf hKK') i
        (formsQuotientMap J delta K hK hd i x) =
      formsQuotientMap L epsilon K' hK' hd' i
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
          epsilon f hf i x) := by
  rw [formsQuotientMap_eq J delta K hK hd, formsQuotientMap_eq L epsilon K' hK' hd']
  exact (mapDifferentialFormsOfDPMorphism_comp (A := A) (J := J) (delta := delta)
    (quotientDividedPowersOfSubDPIdeal J delta K hK)
    (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
    (Ideal.Quotient.mkₐ A K) (Ideal.quotientMapₐ K' f hKK')
    (isDPMorphism_quotientMkₐ J delta K hK)
    (isDPMorphism_quotientMapₐ J delta K hK L epsilon K' hK' f hf hKK')
    (isDPMorphism_quotientComp J delta L epsilon K' hK' f hf) i x).symm.trans
    (mapDifferentialFormsOfDPMorphism_comp (A := A) (J := J) (delta := delta)
    epsilon (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
    f (Ideal.Quotient.mkₐ A K') hf (isDPMorphism_quotientMkₐ L epsilon K' hK')
    (isDPMorphism_quotientComp J delta L epsilon K' hK' f hf) i x)

section Tensor

variable (M : Type*) [AddCommGroup M] [Module C M] [Module (C ⧸ K') M]
  [IsScalarTower C (C ⧸ K') M]

/-- **The second equality of the source's proof of [Stacks, Tag 07LF] is natural in the divided
power ring.**  Its inverse carries `m ⊗ ω` to `m ⊗ (reduction of ω)`, so transporting the second
factor along `f` before applying the inverse over `C` is applying the inverse over `B` and then
transporting along the descent `f̄`.  Pure tensors span, so this determines the square.

The statement is elementwise, on a section of the `C ⧸ K'`-module `M` and a form over `B`, rather
than an equality of two maps `M ⊗_B Ωⁱ_{B/A,δ} ⟶ M ⊗_{C ⧸ K'} Ωⁱ_{(C ⧸ K')/A,ε̄}`: the two
vertical maps of the square are semilinear over *different* base rings in source and target, and
no tensor product of semilinear maps across a square of rings is available to name them with.
Nothing is lost — the transport of the first factor is the identity on `m` on both sides of the
square, so the elementwise form with `m` arbitrary is the whole content. -/
theorem tensorFormsQuotientEquiv_symm_naturality (i : ℕ) (m : M)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    (tensorFormsQuotientEquiv L epsilon K' hK' hd' M i).symm
        (m ⊗ₜ mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
          epsilon f hf i x) =
      m ⊗ₜ mapDifferentialFormsOfDPMorphism (A := A) (J := J.map (Ideal.Quotient.mk K))
        (delta := quotientDividedPowersOfSubDPIdeal J delta K hK)
        (quotientDividedPowersOfSubDPIdeal L epsilon K' hK')
        (Ideal.quotientMapₐ K' f hKK')
        (isDPMorphism_quotientMapₐ J delta K hK L epsilon K' hK' f hf hKK') i
        (formsQuotientMap J delta K hK hd i x) :=
  (tensorFormsQuotientEquiv_symm_tmul L epsilon K' hK' hd' M i m _).trans
    (congrArg (fun z ↦ m ⊗ₜ[C ⧸ K'] z)
      (formsQuotientMap_naturality J delta K hK hd L epsilon K' hK' hd' f hf hKK' i x).symm)

end Tensor

end Naturality

end QuotientFunctorial

/-- **Every ring homomorphism carries `(p)^k` into `(p)^k`**, so a divided power morphism
descends to the finite `p`-adic levels with no hypothesis beyond its existence.  This is the
ring-homomorphism form of `Crystalline.pAdicIdeal_pow_le_comap`, which is stated for a morphism
of `DividedPowerRing` and allows the two levels to differ. -/
theorem pAdicIdeal_pow_le_comap_ringHom {R R' : Type*} [CommRing R] [CommRing R'] (p k : ℕ)
    (f : R →+* R') :
    DividedPowers.pAdicIdeal (A := R) p ^ k ≤
      (DividedPowers.pAdicIdeal (A := R') p ^ k).comap f := by
  rw [← Ideal.map_le_iff_le_comap]
  change Ideal.map f (Ideal.span {(p : R)} ^ k) ≤ Ideal.span {(p : R')} ^ k
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

/-! ### The second equality at a `p`-adic level -/

section PAdicLevel

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (J : Ideal B) (delta : DividedPowers J) (p k : ℕ)
  (hcontained : DividedPowers.pAdicIdeal (A := B) p ^ k ≤ J)
  (hstable : delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ k))

include hcontained hstable

/-- **`Ω^i` of a finite `p`-adic level is the base change of `Ω^i`.**  The two hypotheses are
the two clauses of `Crystalline.IsPAdicLevel`, and the hypothesis `hd` of
`Crystalline.formsQuotientBaseChangeEquiv` on the universal differentials is discharged by
`Crystalline.dividedPowerDifferential_mem_pAdicPow`, so this carries no hypothesis beyond
`k` being a level. -/
def formsLevelBaseChangeEquiv (i : ℕ) :
    (B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k) ⊗[B]
        dividedPowerDifferentialForms (A := A) delta i ≃ₗ[B ⧸
          DividedPowers.pAdicIdeal (A := B) p ^ k]
      dividedPowerDifferentialForms (A := A)
        (DividedPowers.quotientDividedPowers J delta p k hcontained hstable) i :=
  formsQuotientBaseChangeEquiv J delta _ hstable
    (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p k hb) i

/-- **The second equality of the source's proof of [Stacks, Tag 07LF] at a finite `p`-adic
level.**  For a module `M` over the level `B/(p)^k`,

`M ⊗_{B/(p)^k} Ω^i_{(B/(p)^k)/A, δ̄} = M ⊗_B Ω^i_{B/A, δ}`.

This is `Crystalline.tensorFormsQuotientEquiv` at `K = (p)^k`, the quotient divided powers
being the ones `Crystalline.dpQuotientLevelRing` puts on the level.  In the situation of
[Stacks, Tag 07LF], `B` is the completed divided power envelope `D(n)` of
[Stacks, Tag 07J8], `k` is the uniform cutoff `N` plus the `p`-adic level `e`, and `M` is
`M(n)_e`. -/
def tensorFormsLevelEquiv (M : Type*) [AddCommGroup M] [Module B M]
    [Module (B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k) M]
    [IsScalarTower B (B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k) M] (i : ℕ) :
    M ⊗[B ⧸ DividedPowers.pAdicIdeal (A := B) p ^ k]
        dividedPowerDifferentialForms (A := A)
          (DividedPowers.quotientDividedPowers J delta p k hcontained hstable) i ≃ₗ[B ⧸
          DividedPowers.pAdicIdeal (A := B) p ^ k]
      M ⊗[B] dividedPowerDifferentialForms (A := A) delta i :=
  tensorFormsQuotientEquiv J delta _ hstable
    (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p k hb) M i

/-! ### Naturality of the second equality at a `p`-adic level -/

section LevelNaturality

variable {C : Type*} [CommRing C] [Algebra A C] (L : Ideal C) (epsilon : DividedPowers L)
  (hcontained' : DividedPowers.pAdicIdeal (A := C) p ^ k ≤ L)
  (hstable' : epsilon.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := C) p ^ k))
  (f : B →ₐ[A] C) (hf : DividedPowers.IsDPMorphism delta epsilon f.toRingHom)

include hcontained hstable hcontained' hstable' hf

/-- **The second equality of [Stacks, Tag 07LF] at a finite `p`-adic level is natural in the
divided power ring.**

For a divided power morphism `f : (B, J, δ) ⟶ (C, L, ε)` over `A` and a module `M` over the
level `C/(p)^k`, the inverse of `Crystalline.tensorFormsLevelEquiv` intertwines the transport of
forms along `f` with the transport along its descent `f̄ : B/(p)^k ⟶ C/(p)^k` to the levels.
Pure tensors span, so this determines the square; see
`Crystalline.tensorFormsQuotientEquiv_symm_naturality`, of which this is the case
`K = (p)^k`, for why the statement is elementwise rather than an equality of maps.

This is the cosimplicial-direction naturality the source's proof of [Stacks, Tag 07LF] needs of
its second equality: `f` is the transition map `D(n) ⟶ D(m)` of the cosimplicial divided power
envelope of [Stacks, Tag 07L4], `k` is the uniform cutoff plus the level `e`, so `f̄` is the
transition map `D(n)/(p)^{N+e} ⟶ D(m)/(p)^{N+e}` of the level rings, and `M` is `M(m)_e`.
Only the second equality is covered here.  The corresponding statement for the comparison
`Crystalline.tensorFormsCompletionLevelEquiv` of `ModuleDifferentials/CompletionLevelForms.lean`
between the two shapes of `Ω_{D(n)}`, which the isomorphism `ε` of [Stacks, Tag 07LF] needs as
well, is `Crystalline.tensorFormsCompletionLevelEquivAt_naturality` of
`ModuleDifferentials/CompletionLevelFormsNaturality.lean`. -/
theorem tensorFormsLevelEquiv_symm_naturality
    (M : Type*) [AddCommGroup M] [Module C M]
    [Module (C ⧸ DividedPowers.pAdicIdeal (A := C) p ^ k) M]
    [IsScalarTower C (C ⧸ DividedPowers.pAdicIdeal (A := C) p ^ k) M] (i : ℕ) (m : M)
    (x : dividedPowerDifferentialForms (A := A) delta i) :
    (tensorFormsLevelEquiv L epsilon p k hcontained' hstable' M i).symm
        (m ⊗ₜ mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := delta)
          epsilon f hf i x) =
      m ⊗ₜ mapDifferentialFormsOfDPMorphism (A := A)
        (J := J.map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ k)))
        (delta := DividedPowers.quotientDividedPowers J delta p k hcontained hstable)
        (DividedPowers.quotientDividedPowers L epsilon p k hcontained' hstable')
        (Ideal.quotientMapₐ _ f (pAdicIdeal_pow_le_comap_ringHom p k f.toRingHom))
        (isDPMorphism_quotientMapₐ J delta _ hstable L epsilon _ hstable' f hf
          (pAdicIdeal_pow_le_comap_ringHom p k f.toRingHom)) i
        (formsQuotientMap J delta _ hstable
          (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p k hb) i x) :=
  tensorFormsQuotientEquiv_symm_naturality J delta _ hstable
    (fun _ hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p k hb)
    L epsilon _ hstable'
    (fun _ hc ↦ dividedPowerDifferential_mem_pAdicPow (A := A) L epsilon p k hc)
    f hf (pAdicIdeal_pow_le_comap_ringHom p k f.toRingHom) M i m x

end LevelNaturality

end PAdicLevel

end Crystalline

end
