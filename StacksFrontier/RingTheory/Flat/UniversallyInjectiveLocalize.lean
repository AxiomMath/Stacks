module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Localizing the data of a flat base change at a prime

Let `R → S` be a ring map, `N` an `S`-module flat over `R`, `q` a prime of `S` and
`p = q.under R`. The localization `N_q` is flat over the local ring `R_p`, the ring map
`R_p → S_q` is local, and localizing at `q` preserves finite presentation of `N` and flatness of
an `S`-algebra `S'`.

## Main results

* `Stacks.UniversalInjectivity.flat_localizedModule`: if `N` is an `S`-module which is flat over
  a base ring `R` below `S`, then its localization at a submonoid of `S` is still flat over `R`.
* `Stacks.UniversalInjectivity.flat_localizedModule_of_isLocalization` and
  `Stacks.UniversalInjectivity.flat_localizedModule_atPrime`: the same statement over a
  localization of `R`, respectively over the local ring `R_p` with `p = q.under R`.
* `Stacks.UniversalInjectivity.isScalarTower_atPrime_localizedModule`: the `R_p`-action on `N_q`
  of `Stacks.UniversalInjectivity.LocalizationCriteria.moduleRpMq` is compatible with the
  `R`-action.
* `Stacks.UniversalInjectivity.isLocalHom_algebraMap_atPrime`: the canonical map
  `R_p → S_q` of local rings is a local homomorphism.

## References

* [Stacks Project, Tag 05DH](https://stacks.math.columbia.edu/tag/05DH)
* [Stacks Project, Tag 05DG](https://stacks.math.columbia.edu/tag/05DG)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
-/

@[expose] public section

open scoped TensorProduct
open TensorProduct

universe u v w

namespace Stacks.UniversalInjectivity

/-! ### Flatness of a localized module over a base ring -/

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- A module over `S` which is flat over a base ring `R` stays flat over `R` after localizing at
a submonoid of `S`. -/
theorem flat_localizedModule [Module.Flat R N] (T : Submonoid S) :
    Module.Flat R (LocalizedModule T N) := by
  refine Module.Flat.iff_lTensor_injective'.mpr fun I ↦ ?_
  have hlinj := IsLocalizedModule.map_injective T
    (AlgebraTensorModule.rTensor R (↥I) (LocalizedModule.mkLinearMap T N))
    (AlgebraTensorModule.rTensor R R (LocalizedModule.mkLinearMap T N))
    (AlgebraTensorModule.lTensor S N I.subtype) (Module.Flat.iff_lTensor_injective'.mp ‹_› I)
  have nat : (AlgebraTensorModule.lTensor S (LocalizedModule T N) I.subtype) ∘ₗ
      (AlgebraTensorModule.rTensor R (↥I) (LocalizedModule.mkLinearMap T N)) =
      (AlgebraTensorModule.rTensor R R (LocalizedModule.mkLinearMap T N)) ∘ₗ
      (AlgebraTensorModule.lTensor S N I.subtype) := by
    ext n i
    simp
  have heq : IsLocalizedModule.map T
      (AlgebraTensorModule.rTensor R (↥I) (LocalizedModule.mkLinearMap T N))
      (AlgebraTensorModule.rTensor R R (LocalizedModule.mkLinearMap T N))
      (AlgebraTensorModule.lTensor S N I.subtype) =
      AlgebraTensorModule.lTensor S (LocalizedModule T N) I.subtype := by
    refine IsLocalizedModule.linearMap_ext T
      (AlgebraTensorModule.rTensor R (↥I) (LocalizedModule.mkLinearMap T N))
      (AlgebraTensorModule.rTensor R R (LocalizedModule.mkLinearMap T N)) ?_
    rw [IsLocalizedModule.map_comp, nat]
  rwa [heq] at hlinj

/-- The localization of an `S`-module flat over `R` at a submonoid of `S` is flat over any
localization of `R`. -/
theorem flat_localizedModule_of_isLocalization [Module.Flat R N] (T : Submonoid S)
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] (p : Submonoid R) [IsLocalization p Rp]
    [Module Rp (LocalizedModule T N)] [IsScalarTower R Rp (LocalizedModule T N)] :
    Module.Flat Rp (LocalizedModule T N) :=
  (Module.flat_iff_of_isLocalization Rp p (LocalizedModule T N)).mpr (flat_localizedModule T)

/-- The `R_p`-action on `N_q` of `Stacks.UniversalInjectivity.LocalizationCriteria.moduleRpMq`,
which is the `S_q`-action restricted along `R_p → S_q`, is compatible with the `R`-action. -/
instance isScalarTower_atPrime_localizedModule (q : Ideal S) [q.IsPrime] :
    IsScalarTower R (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl N) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)
      (algebraMap R (Localization.AtPrime (q.under R)) r)) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime (q.under R))
      (Localization.AtPrime q), IsScalarTower.algebraMap_smul]

/-- The localization at a prime `q` of `S` of an `S`-module flat over `R` is flat over the local
ring `R_p`, where `p = q.under R`. -/
theorem flat_localizedModule_atPrime [Module.Flat R N] (q : Ideal S) [q.IsPrime] :
    Module.Flat (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl N) :=
  flat_localizedModule_of_isLocalization q.primeCompl
    (Localization.AtPrime (q.under R)) (q.under R).primeCompl

/-! ### The local ring map `R_p → S_q` -/

/-- The canonical map `R_p → S_q` attached to a prime `q` of `S` and its contraction
`p = q.under R` is a local homomorphism of local rings. -/
@[ega "IV 1.3.10" "locality of A_p → B"]
instance isLocalHom_algebraMap_atPrime (q : Ideal S) [q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [IsScalarTower R (Localization.AtPrime (q.under R)) (Localization.AtPrime q)] :
    IsLocalHom (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
  rw [show algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q) =
      Localization.localRingHom (q.under R) q (algebraMap R S) Ideal.LiesOver.over from
    Localization.AtPrime.algebraMap_eq (q.under R) q]
  infer_instance

end Stacks.UniversalInjectivity

end
