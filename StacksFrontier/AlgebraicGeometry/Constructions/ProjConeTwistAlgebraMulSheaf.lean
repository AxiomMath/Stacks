module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPresentation
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.IntegerTwistPower
public import StacksFrontier.AlgebraicGeometry.TwistTensor.MultiplicationAssociativity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplication of `⨁_{m ∈ ℤ} 𝒪_P(m)` is the canonical twist multiplication

The graded algebra `Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra` of all integral
twists on `P = Proj 𝒮` carries its multiplication as a **bilinear map** of sheaves of modules,
`Stacks.AlgebraicGeometry.ProjConeTwist.twistMul`, given on local sections. The canonical
multiplication `𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(a + b)` of [Stacks, Tag 01MO] is the morphism
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`. This file identifies the
two: the morphism
`SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra 𝒮) i j` out of the tensor product
sheaf that the bilinear map descends to **is** `twistMultiplicationMap 𝒮 i j`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.mulSheaf_integerTwistAlgebra_eq_twistMul`:
  `mulSheaf (integerTwistAlgebra 𝒮) i j` equals `twistMultiplicationMap 𝒮 i j` ascribed at the
  tensor-bifunctor spelling, `Stacks.AlgebraicGeometry.TwistTensor.twistMul`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.mulSheaf_integerTwistAlgebra`:
  `mulSheaf (integerTwistAlgebra 𝒮) i j` equals `twistMultiplicationMap 𝒮 i j`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.isIso_pullbackGoodOpen_mulSheaf_integerTwistAlgebra`:
  the multiplication of `⨁_{m ∈ ℤ} 𝒪_P(m)` becomes an isomorphism on the open `W₁` of
  [Stacks, Tag 01MU].

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)
open Stacks.AlgebraicGeometry.TwistTensor (twist_section_ext mulSection_apply)

universe u w

namespace Stacks.AlgebraicGeometry.ProjConeTwist

section Spelling

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The multiplication of `⨁_{m ∈ ℤ} 𝒪_P(m)`, read out of the tensor product sheaf, is the
canonical twist multiplication of [Stacks, Tag 01MO]** — with the latter at the tensor-bifunctor
ascription `Stacks.AlgebraicGeometry.TwistTensor.twistMul`, so that both sides are morphisms out
of the *same* spelling of the tensor product. -/
theorem mulSheaf_integerTwistAlgebra_eq_twistMul (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra 𝒮) i j =
      Stacks.AlgebraicGeometry.TwistTensor.twistMul 𝒮 i j := by
  apply PresheafOfModules.tensorSheaf_hom_ext
  intro U x y
  refine (SheafOfModules.GradedAlgebra.mulSheaf_unit (integerTwistAlgebra 𝒮) i j U x y).trans ?_
  refine twist_section_ext 𝒮 U _ _ fun p => ?_
  exact (mulSection_apply 𝒮 i j U x y p).symm

/-- **The multiplication of `⨁_{m ∈ ℤ} 𝒪_P(m)`, read out of the tensor product sheaf, is
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`**, the canonical
multiplication map of [Stacks, Tag 01MO]. -/
@[ega "II 8.1.5" "partial"]
theorem mulSheaf_integerTwistAlgebra (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra 𝒮) i j =
      twistMultiplicationMap 𝒮 i j :=
  (mulSheaf_integerTwistAlgebra_eq_twistMul 𝒮 i j).trans
    (Stacks.AlgebraicGeometry.TwistTensor.twistMul_eq 𝒮 i j)

end Spelling

section GoodOpen

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The multiplication of `⨁_{m ∈ ℤ} 𝒪_P(m)` becomes an isomorphism on [Stacks, Tag 01MU]'s
open `W₁`**, in every pair of integer degrees. -/
theorem isIso_pullbackGoodOpen_mulSheaf_integerTwistAlgebra (i j : ℤ) :
    IsIso ((modulePullback (GoodOpenIntTwist.goodOpen 𝒮).ι.toLRSHom.toShHom).map
      (SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra 𝒮) i j)) :=
  mulSheaf_integerTwistAlgebra 𝒮 i j ▸ GoodOpenIntTwist.isIso_twistMul 𝒮 i j

end GoodOpen

end Stacks.AlgebraicGeometry.ProjConeTwist

end
