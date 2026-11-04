module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDegreewisePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedPullbackComp
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePasting

/-!
# The derived pasting law for the base change map of abelian small étale sheaves

For two horizontally composable commutative squares of schemes

```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
v           v          v
S₂ --u₂--> S₁ --u₁--> S₀
```

the *derived* base change comparison of the outer rectangle is the composite of the derived
base change comparisons of the two squares, read through the comparisons
$$
R(u_1^{-1}) \circ R(u_2^{-1}) \cong R((u_2 u_1)^{-1}), \qquad
R(v_1^{-1}) \circ R(v_2^{-1}) \cong R((v_2 v_1)^{-1})
$$
of the derived inverse images along the two composite horizontal legs.

The hypotheses are the commutativity of the two squares and nothing else: the squares need not
be cartesian, and no finiteness, separatedness or torsion condition enters.

## Main results

* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste`: **the derived pasting
  law**, as an identity of natural transformations of functors `D⁺(X₀_{ét}) ⥤ D⁺(S₂_{ét})`.
* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app`: the same identity
  evaluated at a bounded below complex.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section DerivedPaste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁)

include w₁ w₂ in
/-- **The derived pasting law for the base change map of abelian small étale sheaves.** The
derived base change comparison of the outer rectangle is the composite of the derived base
change comparisons of the two squares, conjugated by the comparisons of the derived inverse
images along the two composite horizontal legs. -/
theorem smallEtaleDerivedBaseChangeAb_eq_derivedPaste :
    smallEtaleDerivedBaseChangeAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
        (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) =
      Stacks.Cohomology.BaseChange.derivedPaste
        (smallEtalePushforwardAb g₀) (smallEtalePushforwardAb g₁) (smallEtalePushforwardAb g₂)
        (smallEtalePullbackAb u₁) (smallEtalePullbackAb u₂) (smallEtalePullbackAb (u₂ ≫ u₁))
        (smallEtalePullbackAb v₁) (smallEtalePullbackAb v₂) (smallEtalePullbackAb (v₂ ≫ v₁))
        (smallEtalePullbackAbCompIso u₂ u₁) (smallEtalePullbackAbCompIso v₂ v₁)
        (smallEtaleBaseChangeAb u₁ g₀ g₁ v₁ w₁) (smallEtaleBaseChangeAb u₂ g₁ g₂ v₂ w₂) :=
  Stacks.Cohomology.BaseChange.derived_eq_derivedPaste
    (smallEtalePushforwardAb g₀) (smallEtalePushforwardAb g₁) (smallEtalePushforwardAb g₂)
    (smallEtalePullbackAb u₁) (smallEtalePullbackAb u₂) (smallEtalePullbackAb (u₂ ≫ u₁))
    (smallEtalePullbackAb v₁) (smallEtalePullbackAb v₂) (smallEtalePullbackAb (v₂ ≫ v₁))
    (smallEtalePullbackAbCompIso u₂ u₁) (smallEtalePullbackAbCompIso v₂ v₁) _ _ _
    (smallEtaleBaseChangeAb_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)

include w₁ w₂ in
/-- **The derived pasting law, evaluated at a bounded below complex.** -/
theorem smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology X₀) Ab.{u + 1})) :
    (smallEtaleDerivedBaseChangeAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).app M =
      (smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv.app
          ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj M) ≫
        (smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app M) ≫
          (smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
              ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj M) ≫
            (smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
              ((smallEtaleDerivedPullbackAbPlusCompIso v₂ v₁).hom.app M) := by
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedPaste g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂]
  exact Stacks.Cohomology.BaseChange.derivedPaste_app ..

end DerivedPaste

end Stacks.EtaleCohomology

end
