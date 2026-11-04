module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFibreSeparation
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra

/-!
# Flatness over a local ring and over its henselization

Let `A → B` be a local homomorphism of local rings, let `A^h` be a flat local extension of `A`,
let `C` be a pushout of `A → A^h` along `A → B` and let `P` be a prime of `C` lying over the
maximal ideal of `B`. Write `B' = C_P` and `N' = B' ⊗_B N` for a `B`-module `N`. Then `N'` is
flat over `A^h` exactly when `N` is flat over `A`.

This is the sentence "note that `N'` is `A^h`-flat if and only if `N` is `A`-flat" of Claim 1 in
the proof of Stacks 05U9, with `A^h` the henselization of `A` and `P` the maximal ideal
`𝔪_B ⊗ A^h + B ⊗ 𝔪_{A^h}` of `Stacks.ResidueFibre.tensorPrime`.

Both directions are base change and descent. If `N` is `A`-flat then `A^h ⊗_A N` is `A^h`-flat,
`C ⊗_B N` is that module by the pushout identification, and `B'` is flat over `C`, so
`B' ⊗_C (C ⊗_B N) = N'` stays `A^h`-flat by `Stacks.ResidueFibre.flat_baseChange_of_flat`.
Conversely `A^h` is flat over `A`, so `N'` is `A`-flat; the prime `P` lies over the maximal
ideal of `B`, so `B → B'` is a flat local homomorphism of local rings, hence faithfully flat,
and `Module.Flat.tensorProduct_iff_of_faithfullyFlat` — Stacks 0584 (2) — descends `A`-flatness
from `N'` to `N`.

## Main results

* `Stacks.ResidueFibre.flat_tensorProduct_iff_flat_of_isPushout`: the comparison for any `B'`
  which is flat over the pushout and faithfully flat over `B`. This is where both directions are
  proved; the two statements below only exhibit their `B'`.
* `Stacks.ResidueFibre.flat_localization_iff_flat_of_isPushout`: the comparison.
* `Stacks.ResidueFibre.flat_localization_tensorPrime_iff_flat`: the comparison at the
  distinguished prime of `A^h ⊗_A B`, for `A^h` a henselization of `A`.

## References

* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u v w

open IsLocalRing TensorProduct

namespace Stacks.ResidueFibre

section Abstract

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type*} [CommRing A] {Ah : Type*} [CommRing Ah] [Algebra A Ah] [Module.Flat A Ah]
variable {B : Type*} [CommRing B] [Algebra A B]
variable {C : Type*} [CommRing C] [Algebra Ah C] [Algebra B C] [Algebra A C]
  [IsScalarTower A Ah C] [IsScalarTower A B C]
variable {B' : Type*} [CommRing B'] [Algebra C B'] [Algebra Ah B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower Ah C B'] [IsScalarTower B C B'] [IsScalarTower A B B'] [IsScalarTower A Ah B']
  [Module.Flat C B'] [Module.FaithfullyFlat B B']
variable {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- **Flatness over `A` and over a flat extension `A^h` agree after the base change of Claim 1 in
the proof of Stacks 05U9.** Let `C` be a pushout of `A → A^h` along `A → B` and let `B'` be a
`C`-algebra which is flat over `C` and faithfully flat over `B`. Then `B' ⊗_B N` is flat over
`A^h` exactly when `N` is flat over `A`.

Both directions are base change and descent. If `N` is `A`-flat then `A^h ⊗_A N` is `A^h`-flat,
`C ⊗_B N` is that module by the pushout identification, and `B'` is flat over `C`, so
`B' ⊗_C (C ⊗_B N) = B' ⊗_B N` stays `A^h`-flat by `Stacks.ResidueFibre.flat_baseChange_of_flat`.
Conversely `A^h` is flat over `A`, so `B' ⊗_B N` is `A`-flat, and
`Module.Flat.tensorProduct_iff_of_faithfullyFlat` — Stacks 0584 (2) — descends `A`-flatness along
the faithfully flat `B → B'`. -/
theorem flat_tensorProduct_iff_flat_of_isPushout (hpush : Algebra.IsPushout A Ah B C) :
    Module.Flat Ah (B' ⊗[B] N) ↔ Module.Flat A N := by
  have := hpush
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : Module.Flat A (B' ⊗[B] N) := Module.Flat.trans A Ah (B' ⊗[B] N)
    exact (Module.Flat.tensorProduct_iff_of_faithfullyFlat (R := A) (S := B)
      (S' := B') (M := N)).mp inferInstance
  · have : Module.Flat Ah (C ⊗[B] N) :=
      Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A Ah B C N)
    have : Module.Flat Ah (B' ⊗[C] (C ⊗[B] N)) := flat_baseChange_of_flat
    exact Module.Flat.of_linearEquiv
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange B C B' B' N).restrictScalars Ah).symm

end Abstract

section Comparison

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ah : Type u} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah] [Module.Flat A Ah]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
variable {C : Type (max u v)} [CommRing C] [Algebra Ah C] [Algebra B C] [Algebra A C]
  [IsScalarTower A Ah C] [IsScalarTower A B C] [Module.Flat B C]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

omit [IsLocalRing A] [IsLocalRing Ah] [IsLocalHom (algebraMap A B)] in
/-- **Flatness over `A` and over a flat local extension `A^h` agree after the base change of
Claim 1 in the proof of Stacks 05U9.** With `C` a pushout of `A → A^h` along `A → B` and `P` a
prime of `C` lying over the maximal ideal of `B`, the module `C_P ⊗_B N` is flat over `A^h`
exactly when `N` is flat over `A`. -/
theorem flat_localization_iff_flat_of_isPushout
    (hpush : Algebra.IsPushout A Ah B C) (P : Ideal C) [P.IsPrime]
    (hPB : P.comap (algebraMap B C) = IsLocalRing.maximalIdeal B) :
    Module.Flat Ah (Localization.AtPrime P ⊗[B] N) ↔ Module.Flat A N := by
  have : IsLocalHom (algebraMap B (Localization.AtPrime P)) := by
    refine ⟨fun b hb => ?_⟩
    by_contra hbu
    have hbP : algebraMap B C b ∈ P := by
      rw [← Ideal.mem_comap, hPB]
      exact hbu
    have hmem : algebraMap C (Localization.AtPrime P) (algebraMap B C b) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr hbP
    rw [← IsScalarTower.algebraMap_apply B C (Localization.AtPrime P)] at hmem
    exact hmem hb
  have : Module.Flat B (Localization.AtPrime P) :=
    Module.Flat.trans B C (Localization.AtPrime P)
  have : Module.FaithfullyFlat B (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_tensorProduct_iff_flat_of_isPushout hpush

end Comparison

section Henselization

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- **Flatness over a local ring and over its henselization.** Let `A → B` be a local
homomorphism of local rings, let `A^h` be a henselization of `A` and let `B'` be the
localization of `A^h ⊗_A B` at the maximal ideal `𝔪_B ⊗ A^h + B ⊗ 𝔪_{A^h}`. Then `B' ⊗_B N` is
flat over `A^h` exactly when `N` is flat over `A`.

This is the comparison used in Claim 1 of the proof of Stacks 05U9. -/
theorem flat_localization_tensorPrime_iff_flat
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah] :
    Module.Flat Ah
        (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N) ↔
      Module.Flat A N := by
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  have : Module.Flat A Ah := IsLocalRing.IsHenselization.flat (L := ResidueField A)
  have : Module.Flat B (Ah ⊗[A] B) := by
    have : Algebra.IsPushout A B Ah (Ah ⊗[A] B) := Algebra.IsPushout.symm inferInstance
    exact Module.Flat.of_linearEquiv
      (Algebra.IsPushout.equiv A B Ah (Ah ⊗[A] B)).symm.toLinearEquiv
  have : (tensorPrime (A := A) (B := B) Ah).IsPrime := (tensorPrime_isMaximal Ah).isPrime
  exact flat_localization_iff_flat_of_isPushout inferInstance
    (tensorPrime (A := A) (B := B) Ah) (tensorPrime_comap_right Ah)

end Henselization

end Stacks.ResidueFibre

end
