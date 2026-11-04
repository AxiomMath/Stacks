module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# The sections of a pullback along a surjection on functions

Let `f : Y ⟶ X` be a morphism of schemes, `F` a quasi-coherent `𝒪_X`-module, and `U ⊆ X`,
`V ⊆ Y` affine opens with `V ⊆ f⁻¹U` on which the map on functions
`f.appLE U V : Γ(X, U) ⟶ Γ(Y, V)` is **surjective** — the situation of an affine chart of a
closed immersion. Then the pullback-of-sections map

  `Γ(F, U) ⟶ Γ(f^*F, V)`

is surjective, and its kernel is exactly `I · Γ(F, U)` for `I = ker (f.appLE U V)`. In other
words `Γ(f^*F, V) = Γ(F, U)/I·Γ(F, U)`.

This is the statement the conormal algebra of a closed immersion needs: applied to the
degree-`n` piece `ℐⁿ` of the Rees algebra of `ℐ` it says that the degree-`n` sections of the
conormal algebra over an affine chart are `I(U)ⁿ/I(U)ⁿ⁺¹`, which is the local
associated-graded description of [Stacks, Tag 0630].

## Main definitions

* `Stacks.Conormal.surjectiveTensorEquivQuotSMul`: for a surjective algebra map `R ⟶ S` with
  kernel `I` and an `R`-module `M`, the identification `S ⊗[R] M ≃ M ⧸ I • M`.
* `Stacks.Conormal.reesModule`: the degree-`n` piece of the Rees algebra of a quasi-coherent
  ideal sheaf, with its type declared as a module on the scheme.
* `Stacks.Conormal.reesAffineLinearEquiv`: its sections over an affine open `U`, as a
  `Γ(X, U)`-linear equivalence with `I(U)ⁿ`.

## Main results

* `Stacks.Conormal.surjective_one_tmul_eq_zero_iff_mem_smul` and
  `Stacks.Conormal.surjective_one_tmul_surjective_module`: `1 ⊗ₜ m = 0` exactly when `m ∈ I·M`,
  and every element of `S ⊗[R] M` is of the form `1 ⊗ₜ m`. These generalise
  `Stacks.Conormal.surjective_one_tmul_eq_zero_iff` and
  `Stacks.Conormal.surjective_one_tmul_surjective` from `M = Iⁿ` to an arbitrary module.
* `Stacks.Conormal.pullbackSection_eq_zero_iff` and
  `Stacks.Conormal.pullbackSection_surjective`: **the geometric statement.** The pullback of
  sections `Γ(F, U) ⟶ Γ(f^*F, V)` is surjective, and a section pulls back to zero exactly when
  it lies in `I · Γ(F, U)`.
* `Stacks.Conormal.reesPullbackSection_eq_zero_iff` and
  `Stacks.Conormal.reesPullbackSection_surjective`: **the conormal form.** On an affine chart
  `U` whose kernel ideal is `I(U)` and on which the functions surject, the degree-`n` sections
  of `i^*(⨁ₙ Iⁿ)` are `I(U)ⁿ/I(U)ⁿ⁺¹`: every one of them is the pullback of a section of
  `I(U)ⁿ`, and a section of `I(U)ⁿ` pulls back to zero exactly when it lies in `I(U)ⁿ⁺¹`. This
  is the local associated-graded description that [Stacks, Tag 0630] asks of the conormal
  algebra, for the homogeneous pieces taken one at a time.

## Implementation notes

Both geometric statements are read off
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` together with its normalisation
`affinePullbackSectionsBaseChangeIso_one_tmul`: the pullback-of-sections map is, under the
base-change identification, the map `m ↦ 1 ⊗ₜ m`, so the two module-theoretic facts transfer
verbatim. Nothing here uses a description of the sections of a pullback beyond that
isomorphism.

The algebraic half goes through `Stacks.Conormal.quotKerLinearEquiv`, which identifies `S` with
`R ⧸ ker (algebraMap R S)` for a surjective algebra map, and Mathlib's
`TensorProduct.quotTensorEquivQuotSMul`.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.Conormal

/-! ### Base change of a module along a surjection -/

section Surjective

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- **Base change along a surjection is a quotient.** For a surjective algebra map `R ⟶ S` with
kernel `I`, the base change `S ⊗[R] M` of an `R`-module `M` is `M ⧸ I • M`. -/
noncomputable def surjectiveTensorEquivQuotSMul
    (hS : Function.Surjective (algebraMap R S)) (M : Type*) [AddCommGroup M] [Module R M] :
    S ⊗[R] M ≃ₗ[R]
      M ⧸ (RingHom.ker (algebraMap R S) • (⊤ : Submodule R M)) :=
  (TensorProduct.congr (quotKerLinearEquiv hS).symm (LinearEquiv.refl R M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (algebraMap R S)))

/-- The equivalence `surjectiveTensorEquivQuotSMul` sends `1 ⊗ₜ m` to the class of `m` in
`M ⧸ I • M`, where `I` is the kernel of `algebraMap R S`. -/
@[simp]
theorem surjectiveTensorEquivQuotSMul_one_tmul
    (hS : Function.Surjective (algebraMap R S)) (m : M) :
    surjectiveTensorEquivQuotSMul hS M ((1 : S) ⊗ₜ[R] m) = Submodule.Quotient.mk m := by
  have h1 : (quotKerLinearEquiv hS).symm (1 : S) =
      Ideal.Quotient.mk (RingHom.ker (algebraMap R S)) 1 :=
    (quotKerLinearEquiv hS).symm_apply_eq.2 (by rw [← map_one (algebraMap R S)]; rfl)
  rw [surjectiveTensorEquivQuotSMul, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, h1, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]

/-- An element of a module dies in the base change along a surjection exactly when it lies in
the kernel ideal times the module. -/
theorem surjective_one_tmul_eq_zero_iff_mem_smul
    (hS : Function.Surjective (algebraMap R S)) (m : M) :
    (1 : S) ⊗ₜ[R] m = 0 ↔
      m ∈ RingHom.ker (algebraMap R S) • (⊤ : Submodule R M) := by
  rw [← (surjectiveTensorEquivQuotSMul hS M).map_eq_zero_iff,
    surjectiveTensorEquivQuotSMul_one_tmul, Submodule.Quotient.mk_eq_zero]

/-- Every element of a base change along a surjection is of the form `1 ⊗ₜ m`. -/
theorem surjective_one_tmul_surjective_module
    (hS : Function.Surjective (algebraMap R S)) :
    Function.Surjective fun m : M => (1 : S) ⊗ₜ[R] m := by
  intro x
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _
    (surjectiveTensorEquivQuotSMul hS M x)
  refine ⟨m, (surjectiveTensorEquivQuotSMul hS M).injective ?_⟩
  rw [surjectiveTensorEquivQuotSMul_one_tmul, hm]

end Surjective

/-! ### Sections of a pullback over a chart with surjective functions -/

/-- An isomorphism of modules kills only zero. Stated separately so that it is applied, rather
than re-elaborated, at the concrete base-change isomorphism below. -/
private theorem iso_hom_eq_zero_iff {R : Type*} [Ring R] {M N : ModuleCat R} (e : M ≅ N)
    (x : M) : ConcreteCategory.hom e.hom x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective (h.trans (map_zero _).symm)

section Geometric

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
  {U : X.Opens} {V : Y.Opens} (hVU : V ≤ f ⁻¹ᵁ U)

/-- A section pulls back to zero exactly when its image under the base-change identification
vanishes; this is the content-free half of the two statements below. -/
private theorem pullbackSection_eq_zero_iff_tmul
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (a : Γ(F, U)) :
    Scheme.Modules.pullbackSection f F U V hVU a = 0 ↔
      (1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a = 0 := by
  rw [← affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU a]
  exact iso_hom_eq_zero_iff _ _

/-- **The sections of a pullback over a chart on which the functions surject.** A section of
`F` over `U` pulls back to zero on `V` exactly when it lies in `ker (f.appLE U V) · Γ(F, U)`. -/
theorem pullbackSection_eq_zero_iff
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hsurj : Function.Surjective (f.appLE U V hVU).hom) (a : Γ(F, U)) :
    Scheme.Modules.pullbackSection f F U V hVU a = 0 ↔
      a ∈ RingHom.ker (f.appLE U V hVU).hom •
        (⊤ : Submodule Γ(X, U) Γ(F, U)) := by
  let inst : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
  exact (pullbackSection_eq_zero_iff_tmul f F hVU hU hV a).trans
    (surjective_one_tmul_eq_zero_iff_mem_smul (M := Γ(F, U)) hsurj a)

/-- **The sections of a pullback over a chart on which the functions surject.** Every section of
`f^*F` over `V` is the pullback of a section of `F` over `U`. -/
theorem pullbackSection_surjective
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hsurj : Function.Surjective (f.appLE U V hVU).hom) :
    Function.Surjective (Scheme.Modules.pullbackSection f F U V hVU) := by
  let inst : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
  refine Eq.mpr (congrArg Function.Surjective (funext fun a =>
    (affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU a).symm)) ?_
  exact (ConcreteCategory.bijective_of_isIso
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom).surjective.comp
    (surjective_one_tmul_surjective_module (M := Γ(F, U)) hsurj)

end Geometric

/-! ### The conormal pieces of a closed immersion -/

section Rees

/-- The degree-`n` piece of the Rees algebra of an ideal sheaf, with its type *declared* as a
module on the scheme. `AlgebraicGeometry.Scheme.Modules` is a `def` rather than an `abbrev`, so
the category and module instances on `X.Modules` are syntactically different terms from those on
`SheafOfModules X.ringCatSheaf`, which is the type `Stacks.Blowup.reesPiece` is stated at; naming
the piece at `X.Modules` records the right instances once. -/
noncomputable abbrev reesModule {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℤ) : X.Modules :=
  Stacks.Blowup.reesPiece I n

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) (U : X.affineOpens)

/-- The degree-`n` sections of the Rees algebra of `I` over an affine open `U` are the ideal
`I(U)ⁿ`, `Γ(X, U)`-linearly. This is
`Stacks.Blowup.reesPieceAffineEquiv` with its linearity, which is
`Stacks.Blowup.reesPieceAffineEquiv_smul`. -/
noncomputable def reesAffineLinearEquiv :
    Γ(reesModule I (n : ℤ), U.1) ≃ₗ[Γ(X, U)] ↥(I.ideal U ^ n) :=
  { Stacks.Blowup.reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U with
    map_smul' := fun r a => Subtype.ext
      (Stacks.Blowup.reesPieceAffineEquiv_smul I (n : ℤ) (Int.natCast_nonneg n) U r a) }

/-- The linear equivalence `reesAffineLinearEquiv I n U` agrees elementwise with the equivalence
`Stacks.Blowup.reesPieceAffineEquiv`. -/
@[simp]
theorem reesAffineLinearEquiv_apply (a : Γ(reesModule I (n : ℤ), U.1)) :
    reesAffineLinearEquiv I n U a =
      Stacks.Blowup.reesPieceAffineEquiv I (n : ℤ) (Int.natCast_nonneg n) U a := rfl

/-- Transport of `J · M` along a linear equivalence. -/
private theorem mem_smul_top_congr {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (J : Ideal R) (x : M) :
    x ∈ J • (⊤ : Submodule R M) ↔ e x ∈ J • (⊤ : Submodule R N) := by
  have hmap : Submodule.map (e : M →ₗ[R] N) (J • (⊤ : Submodule R M)) =
      J • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top_of_surjective _
      e.surjective]
  rw [← hmap, Submodule.mem_map_equiv]
  simp

variable {Z : Scheme.{u}} (i : Z ⟶ X) (hV : IsAffineOpen (i ⁻¹ᵁ U.1))

include hV in
/-- **The degree-`n` conormal sections of a chart.** On an affine chart `U` whose kernel ideal is
`I(U)` and on which the functions surject — the situation of an affine chart of a closed
immersion with ideal sheaf `I` — a section of `I(U)ⁿ` pulls back to zero in the degree-`n` piece
of `i^*(⨁ₙ Iⁿ)` exactly when it lies in `I(U)ⁿ⁺¹`.

Together with `Stacks.Conormal.reesPullbackSection_surjective` this says that the degree-`n`
sections of `i^*(⨁ₙ Iⁿ)` over the chart are `I(U)ⁿ/I(U)ⁿ⁺¹`: the local associated-graded
description of the conormal algebra, [Stacks, Tag 0630]. -/
theorem reesPullbackSection_eq_zero_iff
    (hker : RingHom.ker (i.app U.1).hom = I.ideal U)
    (hsurj : Function.Surjective (i.app U.1).hom)
    (a : ↥(I.ideal U ^ n)) :
    haveI : (reesModule I (n : ℤ)).IsQuasicoherent :=
      Stacks.Blowup.reesPiece_isQuasicoherent I (n : ℤ)
    Scheme.Modules.pullbackSection i (reesModule I (n : ℤ)) U.1 (i ⁻¹ᵁ U.1) le_rfl
        ((reesAffineLinearEquiv I n U).symm a) = 0 ↔
      (a : Γ(X, U)) ∈ I.ideal U ^ (n + 1) := by
  have := Stacks.Blowup.reesPiece_isQuasicoherent I (n : ℤ)
  rw [← Scheme.Hom.appLE_preimage_self i U.1] at hker hsurj
  rw [pullbackSection_eq_zero_iff i (reesModule I (n : ℤ)) le_rfl U.2 hV hsurj,
    mem_smul_top_congr (reesAffineLinearEquiv I n U) _ _,
    LinearEquiv.apply_symm_apply, hker, smul_top_eq_comap, Submodule.mem_comap,
    Submodule.coe_subtype]

include hV in
/-- **The degree-`n` conormal sections of a chart are all pullbacks.** Every section of the
degree-`n` piece of `i^*(⨁ₙ Iⁿ)` over the chart is the pullback of a section of `I(U)ⁿ`. -/
theorem reesPullbackSection_surjective
    (hsurj : Function.Surjective (i.app U.1).hom) :
    haveI : (reesModule I (n : ℤ)).IsQuasicoherent :=
      Stacks.Blowup.reesPiece_isQuasicoherent I (n : ℤ)
    Function.Surjective fun a : ↥(I.ideal U ^ n) =>
      Scheme.Modules.pullbackSection i (reesModule I (n : ℤ)) U.1 (i ⁻¹ᵁ U.1) le_rfl
        ((reesAffineLinearEquiv I n U).symm a) := by
  have := Stacks.Blowup.reesPiece_isQuasicoherent I (n : ℤ)
  rw [← Scheme.Hom.appLE_preimage_self i U.1] at hsurj
  exact (pullbackSection_surjective i (reesModule I (n : ℤ)) le_rfl U.2 hV hsurj).comp
    (reesAffineLinearEquiv I n U).symm.surjective

end Rees

end Stacks.Conormal

end
