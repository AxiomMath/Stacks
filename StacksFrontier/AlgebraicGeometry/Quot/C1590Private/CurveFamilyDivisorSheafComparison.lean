module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyGoodDivisors
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications

/-!
# The divisor sheaf of a fibre and the pullback of `𝒪(D)`

Let `D` be an effective Cartier divisor on an algebraic space `Y` and `q : h_V ⟶ Y` a morphism
from a scheme whose inverse image of `D` is cut out by an effective Cartier divisor `E` of `V`. We
state the comparison of `q^*𝒪_Y(D)` with `𝒪_V(E)`: vanishing of `H¹` transfers, and so do sections
that are `f · 1_E` away from `E`.

## Main definitions

* `AlgebraicGeometry.C1590Private.FibreDivisorSheafComparison`: the statement that, for such `D`,
  `q` and `E`, vanishing of `H¹(V, 𝒪_V(E))` gives vanishing of `H¹(h_V, q^*𝒪_Y(D))`, and a global
  section of `𝒪_V(E)` equal to `f · 1_E` away from `E` gives a global section of `q^*𝒪_Y(D)`
  equal to `f · q^*1_D` on the étale charts over `V ∖ E`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

namespace AlgebraicGeometry.C1590Private

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Space.hasInjectiveResolutions_modules

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The statement that, for an effective Cartier divisor `D` on an algebraic space `Y` whose
inverse image along `q : h_V ⟶ Y` is the closed subspace cut out by an effective Cartier divisor
`E` of the scheme `V`: (1) vanishing of `H¹(V, 𝒪_V(E))` gives vanishing of `H¹(h_V, q^*𝒪_Y(D))`,
and (2) a global section `t` of `𝒪_V(E)` with `t = f · 1_E` on `V ∖ E` gives a global section `σ`
of `q^*𝒪_Y(D)` with `σ(A) = (f|_A) · (q^*1_D)(A)` on every étale chart `A` of `h_V` lying over
`V ∖ E`. -/
def FibreDivisorSheafComparison : Prop :=
  ∀ (Y : AlgebraicSpaces B integerBase hZ) (V : BigFppfOver B integerBase hZ)
    (q : yoneda.obj V ⟶ Y.obj) (D : Space.ClosedSubspaces B integerBase hZ Y.obj)
    (hD : Space.IsEffectiveCartierDivisor B integerBase hZ Y D)
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData)
    (_ : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (_ : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1),
    (IsZero (Hgroup ((BigFppfOver.toScheme B integerBase hZ).obj V).ringCatSheaf ⊤ 1
        (Stacks.Divisors.divisorSheaf E)) →
      Limits.IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
          (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived 1).obj
          ((Space.modulePullback B integerBase hZ (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
            (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)))) ∧
    ∀ (t : Γ(Stacks.Divisors.divisorSheaf E, ⊤))
      (f : Γ((BigFppfOver.toScheme B integerBase hZ).obj V, E.support.compl)),
      (Stacks.Divisors.divisorSheaf E).presheaf.map
          (homOfLE (le_top : E.support.compl ≤ ⊤)).op t =
        f • (Stacks.Divisors.divisorSheaf E).presheaf.map
          (homOfLE (le_top : E.support.compl ≤ ⊤)).op
          (Stacks.Divisors.divisorSheafGlobalSection E) →
      ∃ σ : (globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B integerBase hZ
            (schemeSpace V).1 (schemeSpace V).2).O)).obj
          ((Space.modulePullback B integerBase hZ (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
            (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)),
        ∀ (U : Space.SmallEtale B integerBase hZ (yoneda.obj V))
          (hU : ⊤ ≤ (BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage U.1.hom) ⁻¹ᵁ
            E.support.compl),
          (show ((Space.modulePullback B integerBase hZ
                (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
                (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)).val.obj (op U) from
            σ.1 (op U)) =
            (show Space.chartRing B integerBase hZ (schemeSpace V).1 (schemeSpace V).2 U from
              ((BigFppfOver.toScheme B integerBase hZ).map (yoneda.preimage U.1.hom)).appLE
                E.support.compl ⊤ hU f) •
              (show ((Space.modulePullback B integerBase hZ
                  (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
                  (Space.associatedInvertibleSheaf B integerBase hZ Y D hD)).val.obj (op U) from
                ((Space.globalSectionsPullbackMap B integerBase hZ
                  (ObjectProperty.homMk q : schemeSpace V ⟶ Y) _).hom
                  (Space.canonicalSection B integerBase hZ Y D hD)).1 (op U))

end AlgebraicGeometry.C1590Private

end
