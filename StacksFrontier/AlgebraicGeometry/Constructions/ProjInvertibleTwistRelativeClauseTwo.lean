module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeThetaConcrete

/-!
# Clause (2) of Tag 02NC over a base scheme

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module,
`ℬ = ⨁_n 𝒜_n ⊗ ℒ^{⊗ n}` the twist, `π : P = Proj_S(𝒜) ⟶ S`, `π' : P' = Proj_S(ℬ) ⟶ S`, and
`g : P ⟶ P'` the canonical isomorphism over `S` with its comparisons
`θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`. Clause (2) of Tag 02NC asserts that for every open
`V ⊆ S` the square

```
𝒜_n(V) ⊗ ℒ^{⊗ n}(V) ------- multiply -------> ℬ_n(V)
        |                                        |
        | ψ ⊗ π^*                                | ψ
        v                                        v
Γ(π^{-1}V, 𝒪_P(n)) ⊗ Γ(π^{-1}V, π^*ℒ^{⊗ n})    Γ(π'^{-1}V, 𝒪_{P'}(n))
        |                                        |
        | multiply                               | θ_n
        v                                        v
Γ(π^{-1}V, 𝒪_P(n) ⊗ π^*ℒ^{⊗ n})  ============  Γ(π^{-1}V, 𝒪_P(n) ⊗ π^*ℒ^{⊗ n})
```

commutes, `ψ` being the homogeneous-section maps of Tag 01NR.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistTheta_clauseTwo`: **clause (2) of Tag
  02NC**, for the tag's `g = relativeTwistHom L 𝒜` and `θ_n = twistThetaIso L 𝒜 n`, over every open
  of the base and in every degree.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.clauseTwo_of_phi`: the square for the
  comparison obtained from any identification `Φ` of `⨁_n 𝒪_{P'}(n)` with the transported target
  that carries the homogeneous sections of `ℬ` to the *multiply* map.

## Implementation notes

`θ_n` acts on sections over `π'^{-1}V` through
`Stacks.AlgebraicGeometry.RelativeTwistSections.thetaSections`: a section of `𝒪_{P'}(n)` is
carried by the unit of `g^* ⊣ g_*` to a section of `g^*𝒪_{P'}(n)` over `g^{-1}π'^{-1}V = π^{-1}V`
and mapped by `θ_n`. The two *multiply* maps are the canonical maps into the sections of a tensor
product of sheaves of modules, `Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTmul` on
pure tensors and `gammaTensorMap` on the whole tensor product; the lower route on the whole tensor
product is `Stacks.AlgebraicGeometry.RelativeTwistSections.lowerRoute`. The square is stated both
on pure tensors and on the whole tensor product `𝒜_n(V) ⊗_{Γ(S, V)} ℒ^{⊗ n}(V)`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.AffineOpenTensorSections
open Stacks.AlgebraicGeometry.RelativeTwistSections
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- The square of clause (2) for the comparison `globalThetaIso L 𝒜 Φ`, on pure tensors and on
the whole tensor product, for an identification `Φ` carrying the homogeneous-section map of
`Proj_S(ℬ)` to the transported *multiply* map. -/
theorem clauseTwo_of_phi (Φ : Tag07ZGTwist.twistAlgebra (twist 𝒜 L) ≅ transportedTarget L 𝒜)
    (hΦ : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map (Φ.hom.app k) =
        transportedPsi L 𝒜 k)
    (V : S.Opens) (n : ℕ) :
    (∀ (a : Γ(𝒜.piece (n : ℤ), V)) (l : Γ(tpMod L (n : ℤ), V)),
      thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
          (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
          (globalThetaIso L 𝒜 Φ n).hom V
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
            (gammaTmul (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V a l)) =
        gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 n)
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))
          ((relativeProj 𝒜).toBase ⁻¹ᵁ V)
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n).val.app (op V) a)
          (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj 𝒜).toBase).unit.app
            (tpMod L n)).val.app (op V) l)) ∧
    ∀ z : Γ(𝒜.piece (n : ℤ), V) ⊗[Γ(S, V)] Γ(tpMod L (n : ℤ), V),
      thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
          (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
          (globalThetaIso L 𝒜 Φ n).hom V
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
            (gammaTensorMap (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V z)) =
        lowerRoute (relativeProj 𝒜).toBase ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n)
          V z :=
  ⟨globalTheta_squareAt L 𝒜 Φ hΦ n V,
    upperRoute_eq_lowerRoute (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
      (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n)
      (globalThetaIso L 𝒜 Φ n).hom (globalTheta_squareAt L 𝒜 Φ hΦ n V)⟩

/-- **Stacks Project, Tag 02NC, clause (2).** Let `S` be a scheme, `𝒜` a quasi-coherent graded
`𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module and `ℬ = ⨁_n 𝒜_n ⊗ ℒ^{⊗ n}` its twist; let
`π : P = Proj_S(𝒜) ⟶ S`, `π' : P' = Proj_S(ℬ) ⟶ S`, let `g = relativeTwistHom L 𝒜 : P ⟶ P'` be the
canonical isomorphism over `S` and `θ_n = twistThetaIso L 𝒜 n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`
its comparisons. Then **for every open `V ⊆ S` and every `n`** the square of clause (2) commutes:
the route `𝒜_n(V) ⊗ ℒ^{⊗ n}(V) → ℬ_n(V) → Γ(π'^{-1}V, 𝒪_{P'}(n)) → Γ(π^{-1}V, 𝒪_P(n) ⊗ π^*ℒ^{⊗ n})`
through the multiplication, the homogeneous-section map `ψ` of `ℬ` and `θ_n` equals the route
`ψ ⊗ π^*` followed by the multiplication
`Γ(π^{-1}V, 𝒪_P(n)) ⊗ Γ(π^{-1}V, π^*ℒ^{⊗ n}) → Γ(π^{-1}V, 𝒪_P(n) ⊗ π^*ℒ^{⊗ n})`.

The first conjunct is the square on pure tensors `a ⊗ l`; the second is the same square as an
equality of maps out of the whole tensor product `𝒜_n(V) ⊗_{Γ(S, V)} ℒ^{⊗ n}(V)`, the lower route
being `Stacks.AlgebraicGeometry.RelativeTwistSections.lowerRoute`. `θ_n` acts on sections through
`Stacks.AlgebraicGeometry.RelativeTwistSections.thetaSections` (the unit of `g^* ⊣ g_*`, then
`θ_n`, over `g^{-1}π'^{-1}V = π^{-1}V`). The graded rings are `ℕ`-graded, so the degrees with a
nonzero piece `𝒜_n` are `n : ℕ`.

This is the clause-(2) part of the whole tag, for the whole-tag statement to cite. -/
theorem twistTheta_clauseTwo (V : S.Opens) (n : ℕ) :
    (∀ (a : Γ(𝒜.piece (n : ℤ), V)) (l : Γ(tpMod L (n : ℤ), V)),
      thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
          (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
          (twistThetaIso L 𝒜 n).hom V
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
            (gammaTmul (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V a l)) =
        gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 n)
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))
          ((relativeProj 𝒜).toBase ⁻¹ᵁ V)
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n).val.app (op V) a)
          (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj 𝒜).toBase).unit.app
            (tpMod L n)).val.app (op V) l)) ∧
    ∀ z : Γ(𝒜.piece (n : ℤ), V) ⊗[Γ(S, V)] Γ(tpMod L (n : ℤ), V),
      thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
          (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
          (twistThetaIso L 𝒜 n).hom V
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
            (gammaTensorMap (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V z)) =
        lowerRoute (relativeProj 𝒜).toBase ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n)
          V z :=
  clauseTwo_of_phi L 𝒜 (twistThetaPhi L 𝒜) (twistThetaPhi_psi L 𝒜) V n

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
