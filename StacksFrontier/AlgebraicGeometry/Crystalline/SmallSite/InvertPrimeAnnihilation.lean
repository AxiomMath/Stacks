module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusInvertPrime

/-!
# Annihilation of kernel and cokernel by a power of `p` makes a map invertible after inverting `p`

[Stacks, Tag 07QA] and [Stacks, Tag 07QB] conclude about their maps that the *kernel and cokernel
of each cohomology group map are annihilated by a power of `p`*.  The conclusion of
[Stacks, Tag 07N5] is that a map of `D(A)` *becomes an isomorphism after inverting `p`*,
`Crystalline.GlobalCrystallineSituation.SmallSite.BecomesIsoAfterInvertingPrime`.  This file is
the passage from the first form to the second.

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusInvertPrime.lean` explains why the
two are not interchangeable: annihilation by a *fixed* power of `p` of the kernel and cokernel of
the map itself is strictly stronger than becoming an isomorphism after inverting `p`.  What is
proved here is the implication that does hold, and in the degreewise form the source's bounds
have: if for **every** `n` there is some `k` with the kernel and the cokernel of
`Hⁿ(φ) : Hⁿ(X) ⟶ Hⁿ(Y)` annihilated by `p ^ k` — the exponent may grow with `n`, as it does in
[Stacks, Tag 07QB], where it is `p ^ (d(n+1))` — then `φ` becomes an isomorphism after inverting
`p`.

## The argument

Inverting `p` is the functor induced degreewise by the *exact* functor `- ⊗_A A[1/p]`
(`...SmallSite.invertPrime`), so two general facts suffice.

* An exact functor commutes with the homology of the derived category, and therefore inverts a
  morphism exactly when it inverts each of its homology maps:
  `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`.
* Extension of scalars along `A ⟶ A[1/p]` is exact, hence preserves kernels and cokernels; and a
  module over `A[1/p]` annihilated by `p ^ k` is zero, because `p` is a unit there.  So the
  kernel and the cokernel of the image of `Hⁿ(φ)` vanish, and a map in an abelian category with
  zero kernel and zero cokernel is an isomorphism.

No boundedness, no finiteness and no completeness is used: the exponent is allowed to depend on
the degree and nothing relates the degrees to one another.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isIso_nsmul_id_invertPrimeModule` — `p ^ k` acts invertibly on every `A[1/p]`-module.
* `isZero_of_nsmul_id_eq_zero` — an `A[1/p]`-module annihilated by `p ^ k` is zero.
* `isIso_extendScalars_map_of_annihilation` — a map of `A`-modules whose kernel and cokernel are
  annihilated by `p ^ k` becomes an isomorphism after extension of scalars to `A[1/p]`.
* `becomesIsoAfterInvertingPrime_of_homology_annihilation` — **the passage from the
  [Stacks, Tag 07QA] form of a bound to the [Stacks, Tag 07N5] form of a conclusion**: a morphism
  of `D(Mod_A)` each of whose homology maps has kernel and cokernel annihilated by some power of
  `p` becomes an isomorphism after inverting `p`.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u wA wP

noncomputable section

namespace CategoryTheory.Functor

/-- **An additive functor carries an object annihilated by `n` to an object annihilated by
`n`.**  `n • 𝟙 Z = 0` says that `n` times the identity of `Z` vanishes, and an additive functor
preserves identities, `ℕ`-multiples and the zero morphism. -/
theorem nsmul_id_obj_eq_zero {C : Type*} {D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {Z : C} {n : ℕ}
    (h : n • 𝟙 Z = 0) : n • 𝟙 (F.obj Z) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

/-- **An exact functor inverts a map whose kernel and cokernel it kills.**  An exact functor
preserves kernels and cokernels, so if it sends the kernel and the cokernel of `ψ` to zero
objects then its image of `ψ` has zero kernel and zero cokernel, and in an abelian category such
a map is an isomorphism. -/
theorem isIso_map_of_isZero_kernel_cokernel {C : Type*} {D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] {M N : C} (ψ : M ⟶ N)
    (hk : Limits.IsZero (F.obj (Limits.kernel ψ)))
    (hc : Limits.IsZero (F.obj (Limits.cokernel ψ))) : IsIso (F.map ψ) := by
  have hk' : Limits.IsZero (Limits.kernel (F.map ψ)) :=
    hk.of_iso (Limits.PreservesKernel.iso F ψ).symm
  have hc' : Limits.IsZero (Limits.cokernel (F.map ψ)) :=
    hc.of_iso (Limits.PreservesCokernel.iso F ψ).symm
  have : Mono (F.map ψ) := Abelian.mono_of_kernel_ι_eq_zero _ (hk'.eq_zero_of_src _)
  have : Epi (F.map ψ) := Abelian.epi_of_cokernel_π_eq_zero _ (hc'.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

end CategoryTheory.Functor

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **`p ^ k` acts invertibly on every `A[1/p]`-module.**  The category of `A[1/p]`-modules is
`A[1/p]`-linear and `p` is a unit of `A[1/p]`, that ring being the localization of `A` at a
submonoid containing `p`.

This is the underived twin of `...SmallSite.isIso_nsmul_id_invertPrime_obj`. -/
theorem isIso_nsmul_id_invertPrimeModule (k : ℕ) (Z : ModuleCat.{u + 1} (invertPrimeRing S)) :
    IsIso ((S.p ^ k) • 𝟙 Z) := by
  have h : IsUnit (algebraMap ↥Γ(S.S.scheme, ⊤) (invertPrimeRing S) (S.p : Γ(S.S.scheme, ⊤))) :=
    IsLocalization.map_units (invertPrimeRing S)
      ⟨(S.p : Γ(S.S.scheme, ⊤)), Submonoid.mem_powers _⟩
  rw [map_natCast] at h
  obtain ⟨v, hv⟩ := h.pow k
  rw [← Nat.cast_smul_eq_nsmul (invertPrimeRing S), Nat.cast_pow, ← hv]
  refine ⟨⟨((v⁻¹ : (invertPrimeRing S)ˣ) : invertPrimeRing S) • 𝟙 _, ?_, ?_⟩⟩
  · rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.mul_inv, one_smul]
  · rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.inv_mul, one_smul]

/-- **An `A[1/p]`-module annihilated by `p ^ k` is zero.**  `p ^ k` acts both invertibly and as
zero on it, so its identity is zero. -/
theorem isZero_of_nsmul_id_eq_zero {k : ℕ} {Z : ModuleCat.{u + 1} (invertPrimeRing S)}
    (h : (S.p ^ k) • 𝟙 Z = 0) : IsZero Z := by
  have hiso := isIso_nsmul_id_invertPrimeModule S k Z
  rw [h] at hiso
  rw [IsZero.iff_id_eq_zero]
  have hid : (0 : Z ⟶ Z) ≫ inv (0 : Z ⟶ Z) = 𝟙 Z := IsIso.hom_inv_id (0 : Z ⟶ Z)
  rw [zero_comp] at hid
  exact hid.symm

/-- **A map of `A`-modules whose kernel and cokernel are annihilated by `p ^ k` becomes an
isomorphism after extension of scalars to `A[1/p]`.**

Extension of scalars along `A ⟶ A[1/p]` is exact, by flatness of the localization
(`...SmallSite.invertPrimeRingHom_flat`), so it carries the kernel and the cokernel of `ψ` to the
kernel and the cokernel of its image; each of those is annihilated by `p ^ k` and hence zero by
`isZero_of_nsmul_id_eq_zero`, which makes the image a monomorphism and an epimorphism, hence an
isomorphism. -/
theorem isIso_extendScalars_map_of_annihilation {M N : ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤)}
    (ψ : M ⟶ N) {k : ℕ}
    (hker : (S.p ^ k) • 𝟙 (kernel ψ) = 0) (hcoker : (S.p ^ k) • 𝟙 (cokernel ψ) = 0) :
    IsIso ((ModuleCat.extendScalars.{u, u, u + 1} (invertPrimeRingHom S)).map ψ) :=
  Functor.isIso_map_of_isZero_kernel_cokernel _ ψ
    (isZero_of_nsmul_id_eq_zero S (Functor.nsmul_id_obj_eq_zero _ hker))
    (isZero_of_nsmul_id_eq_zero S (Functor.nsmul_id_obj_eq_zero _ hcoker))

variable [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing S))]

/-- **From the bound of [Stacks, Tag 07QA] to the conclusion of [Stacks, Tag 07N5].**

A morphism of `D(Mod_A)` whose homology map in each degree has kernel and cokernel annihilated by
some power of `p` becomes an isomorphism after inverting `p`.  The exponent is allowed to depend
on the degree, which is what [Stacks, Tag 07QB] delivers: there it is `p ^ (d(n+1))`.

Inverting `p` is induced by an exact functor, so it inverts a morphism exactly when it inverts
each of the morphism's homology maps
(`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`), and
`isIso_extendScalars_map_of_annihilation` does each of those. -/
theorem becomesIsoAfterInvertingPrime_of_homology_annihilation
    {X Y : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))} (φ : X ⟶ Y)
    (h : ∀ n : ℤ, ∃ k : ℕ,
      (S.p ^ k) • 𝟙 (kernel ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤)) n).map φ)) = 0 ∧
      (S.p ^ k) • 𝟙 (cokernel ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} ↥Γ(S.S.scheme, ⊤)) n).map φ)) = 0) :
    BecomesIsoAfterInvertingPrime S φ := by
  show IsIso ((invertPrime S).map φ)
  rw [invertPrime, Functor.isIso_mapDerivedCategory_map_iff]
  intro n
  obtain ⟨k, hker, hcoker⟩ := h n
  exact isIso_extendScalars_map_of_annihilation S _ hker hcoker

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
