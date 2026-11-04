module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulRestrict
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Reading sections and tensor powers on an open subscheme

Two transport statements used in the proof of [Stacks, Tag 07RM], where the sections of a
power of a relatively ample invertible module over the preimage of an affine open of the base are
read as global sections on that open subscheme.

## Main results

* `Stacks.QuasiProjectiveCompactification.restrictPowSection_surjective`: every global section of
  `(M|_U)^{⊗ n}` on the open subscheme `U` comes from a section of `M^{⊗ n}` over `U`.
* `Stacks.QuasiProjectiveCompactification.nonempty_natTensorPow_pullback_iso`: the first tensor
  power of `(L^{⊗ d})|_U` is `(L|_U)^{⊗ d}`.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.QuasiProjectiveCompactification

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **Every global section of `(M|_U)^{⊗ n}` on the open subscheme `U` is the restriction of a
section of `M^{⊗ n}` over `U`.** `restrictPowSection` is the bare restriction of sections,
which is a bijection onto the global sections of `(M^{⊗ n})|_U`, followed by the comparison
isomorphism `(M^{⊗ n})|_U ≅ (M|_U)^{⊗ n}`. -/
theorem restrictPowSection_surjective {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (U : Y.Opens) (n : ℕ) :
    Function.Surjective
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection M U n) := by
  intro y
  let e := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictNatTensorPowIso M U n
  refine ⟨Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection U (natTensorPow M n)
    (Scheme.Modules.Hom.app e.inv ⊤ y), ?_⟩
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection_eq M U n
    _).trans ((congrArg (Scheme.Modules.Hom.app e.hom ⊤)
      (Stacks.NonvanishingLocusRestrict.restrictSection_sectionOfRestrictGlobalSection U
        (natTensorPow M n) _)).trans ?_)
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ y) e.inv_hom_id

/-- **The first tensor power of `(L^{⊗ d})|_U` is `(L|_U)^{⊗ d}`**: the first tensor power is the
module itself, by the left unitor, and the restriction of `L^{⊗ d}` is `(L|_U)^{⊗ d}` by
[Stacks, Tag 01CD]. -/
theorem nonempty_natTensorPow_pullback_iso {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (U : X.Opens) (d : ℕ) :
    Nonempty (natTensorPow ((Scheme.Modules.pullback U.ι).obj
        (Stacks.Ample.tensorPowModule X L d)) 1 ≅
      Stacks.Ample.tensorPowModule U.toScheme
        ((RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom).obj L) d) :=
  ⟨λ_ _ ≪≫ Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso U.ι L d⟩

end Stacks.QuasiProjectiveCompactification

end
