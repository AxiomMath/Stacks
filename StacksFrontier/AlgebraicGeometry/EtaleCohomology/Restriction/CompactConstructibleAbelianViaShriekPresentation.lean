module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Constructible abelian sheaves on the small étale site are compact

Let `X` be a quasi-compact and quasi-separated scheme. Morphisms out of a constructible abelian
sheaf on `X_étale` commute with filtered colimits: for a filtered colimit `G = colim G_i` of
abelian sheaves, `Mor(F, G) = colim Mor(F, G_i)`. This is the sheaves-of-abelian-groups case of
Stacks 09Z4.

An abelian sheaf is a sheaf of `ℤ`-modules and `ℤ` is Noetherian, so this is the module case at
`Λ = ℤ`. Under the equivalence `AddCommGrpCat ≌ ModuleCat ℤ` a constructible abelian sheaf becomes
a constructible sheaf of `ℤ`-modules
(`AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence`). Stacks 095N at `ℤ`
presents it as the cokernel of a map between finite direct sums of extensions by zero of the
constant sheaf `ℤ` at quasi-compact and quasi-separated étale objects; that is
`AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`, which reads the
library's Stacks 095N at the Noetherian ring `ULift ℤ` and transports it back to `ℤ`. Such a
presentation forces compactness
(`AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation_int`), and compactness is
carried back across the equivalence.

## Main results

* `AlgebraicGeometry.IsConstructibleAbelianSheaf.isFinitelyPresentable` — **the
  sheaves-of-abelian-groups case of Stacks 09Z4**: a constructible abelian sheaf on the small
  étale site of a quasi-compact and quasi-separated scheme is a compact object.

## Implementation notes

Compactness is `CategoryTheory.IsFinitelyPresentable`, which says that the covariant Hom functor
preserves filtered colimits; that is exactly the assertion that the canonical map
`colim Mor(F, G_i) → Mor(F, colim G_i)` is a bijection.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- **The sheaves-of-abelian-groups case of Stacks 09Z4.** Let `X` be a quasi-compact and
quasi-separated scheme and let `F` be a constructible abelian sheaf on `X_étale`. Then morphisms
out of `F` commute with filtered colimits of abelian sheaves:
`Mor(F, colim G_i) = colim Mor(F, G_i)`.

A constructible abelian sheaf is a constructible sheaf of `ℤ`-modules and `ℤ` is Noetherian, so
this is the module case at `Λ = ℤ`. Stacks 095N at `ℤ`, the presentation of a constructible sheaf
of `ℤ`-modules as the cokernel of a map between finite direct sums of extensions by zero of the
constant sheaf `ℤ` at quasi-compact and quasi-separated étale objects, is supplied by
`AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`. -/
@[stacks 09Z4 "sheaves of abelian groups"]
public theorem IsConstructibleAbelianSheaf.isFinitelyPresentable
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsFinitelyPresentable.{u + 1} F :=
  let := fun (S T : B.Scheme) (f : T ⟶ S) ↦
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, u + 1, 0} B ℤ f
  let := fun (T : B.Scheme) (V : SmallEtale B T.1 T.property) ↦
    SmallEtale.hasWeakSheafifyOver_moduleCat.{u, u + 1, 0} B ℤ T V
  (isCardinalPresentable_iff_of_isEquivalence F Cardinal.aleph0.{u + 1}
    (Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor).1
    (isFinitelyPresentable_of_hasFiniteShriekPresentation_int B X _
      (fun W hW ↦ SmallEtale.hasFiniteQuasiCompactCoverings B X W hW.1 hW.2) _
      (hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int B X _
        (isConstructibleModuleSheaf_moduleCatIntEquivalence B X F hF)))

end AlgebraicGeometry

end
